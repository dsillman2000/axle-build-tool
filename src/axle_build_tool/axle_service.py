"""Async service layer around the `axiom-axle` SDK.

Owns `AxleClient` construction (the SDK reads `AXLE_API_URL`,
`AXLE_MAX_CONCURRENCY`, `AXLE_TIMEOUT_SECONDS`, and `AXLE_API_KEY` from
the environment itself) and applies the project's `axle` settings
(`environment`, `timeout_seconds`, `global_options`) to every request.
API errors are translated into `AxleServiceError` with actionable,
user-facing messages.

When the project does not pin `axle.environment`, the service picks the
latest Lean environment the API offers, using the SDK's
`get_latest_environment`; if the API is unreachable it falls back to
`FALLBACK_ENVIRONMENT`.

The CLI stays synchronous; command bodies run these coroutines via
`asyncio.run`. Tests inject a fake client through `client_factory`.
"""

from __future__ import annotations

import difflib
import logging
from collections.abc import Callable
from typing import Any

import aiohttp
from axle.client import AxleClient
from axle.exceptions import (
    AxleApiError,
    AxleError,
    AxleForbiddenError,
    AxleInvalidArgument,
    AxleIsUnavailable,
    AxleRateLimitedError,
    LeanResourceExceeded,
    LeanTimeout,
)
from axle.types import (
    CheckResponse,
    ExtractDeclsResponse,
    Theorem2SorryResponse,
    VerifyProofResponse,
)

from axle_build_tool.config import AxleConfig, FALLBACK_ENVIRONMENT

logger = logging.getLogger(__name__)

#: Factory signature so tests can substitute a fake client.
ClientFactory = Callable[[], Any]


class AxleServiceError(Exception):
    """Raised when an Axle API interaction fails.

    The message is user-facing and actionable; `__cause__` keeps the
    original SDK exception.
    """


def describe_axle_error(exc: AxleError, config: AxleConfig, context: str) -> str:
    """Translate an SDK exception into an actionable one-line message."""
    if isinstance(exc, AxleIsUnavailable):
        detail = (
            f"Axle API at '{AxleClient.DEFAULT_URL}' is unreachable ({exc}). "
            "Check your connection, or set AXLE_API_URL to point at your Axle server."
        )
    elif isinstance(exc, AxleForbiddenError):
        detail = (
            f"Axle API rejected the request ({exc}). "
            "Set AXLE_API_KEY to a valid API key and try again."
        )
    elif isinstance(exc, AxleRateLimitedError):
        detail = (
            f"Axle API rate limit hit ({exc}). "
            "Wait a moment and retry; consider lowering request concurrency."
        )
    elif isinstance(exc, LeanTimeout):
        detail = (
            f"The Axle request timed out ({exc}). "
            f"Raise 'axle.timeout_seconds' (currently {config.timeout_seconds}) "
            "in axbt_project.yml."
        )
    elif isinstance(exc, LeanResourceExceeded):
        detail = (
            f"The Axle request exceeded Lean resource limits ({exc}). "
            "Raise limits via 'axle.global_options' (e.g. maxHeartbeats) or "
            "simplify the submitted code."
        )
    elif isinstance(exc, AxleInvalidArgument):
        detail = f"Axle API rejected the request as invalid ({exc})."
    elif isinstance(exc, AxleApiError):
        detail = f"Axle API error ({exc})."
    else:
        detail = f"Axle error ({exc})."
    if context:
        return f"{context}: {detail}"
    return detail


class AxleService:
    """Project-aware wrapper around `AxleClient`.

    Applies the `axle` section of `axbt_project.yml` to every call and
    translates SDK exceptions into `AxleServiceError`. The client is
    created lazily via `client_factory` so tests can inject fakes.
    """

    def __init__(
        self,
        config: AxleConfig,
        client_factory: ClientFactory = AxleClient,
    ) -> None:
        self._config = config
        self._client_factory = client_factory
        self._client: Any | None = None
        self._resolved_environment: str | None = None
        self._environment_validated = False

    @property
    def client(self) -> Any:
        if self._client is None:
            self._client = self._client_factory()
        return self._client

    @property
    def max_concurrency(self) -> int:
        """Max concurrent in-flight requests (from the client; default 4)."""
        return int(getattr(self.client, "max_concurrency", 4))

    async def resolve_environment(self) -> str:
        """Resolve the environment for an API call.

        An explicitly configured `axle.environment` is used verbatim.
        Otherwise (the default) axbt pings the Axle API's environments
        endpoint and picks the latest Lean version it offers, via the
        SDK's `get_latest_environment`; the resolved value is cached for
        the lifetime of the service. If the Axle API is unreachable, the
        ultimate fallback is `FALLBACK_ENVIRONMENT` so a best-effort
        attempt can still be made; any other detection error propagates.
        """
        if self._config.environment is not None:
            return self._config.environment
        if self._resolved_environment is None:
            try:
                latest = await self.client.get_latest_environment(
                    timeout_seconds=self._config.timeout_seconds
                )
            except AxleIsUnavailable as exc:
                logger.warning(
                    "Could not reach the Axle API to pick the latest Lean "
                    "environment (%s); falling back to %s",
                    exc,
                    FALLBACK_ENVIRONMENT,
                )
                self._resolved_environment = FALLBACK_ENVIRONMENT
            except AxleError as exc:
                raise AxleServiceError(
                    describe_axle_error(
                        exc, self._config, context="picking the default environment"
                    )
                ) from exc
            else:
                if latest is None:
                    logger.warning(
                        "The Axle API listed no Lean environments; "
                        "falling back to %s",
                        FALLBACK_ENVIRONMENT,
                    )
                    self._resolved_environment = FALLBACK_ENVIRONMENT
                else:
                    self._resolved_environment = latest["name"]
        return self._resolved_environment

    async def validate_environment(self) -> None:
        """Validate an explicitly pinned `axle.environment` against the API.

        The default (auto-selected) environment needs no validation — it
        is picked from this very endpoint. A pinned value, however, is
        otherwise passed verbatim to every API call and would only fail
        opaquely at submission time, so check it (once per service
        lifetime) and raise `AxleServiceError` naming the available
        environments — with a close-match hint — when the API does not
        serve it.
        """
        if self._config.environment is None or self._environment_validated:
            return
        available = sorted(
            str(entry["name"])
            for entry in await self.environments(timeout_seconds=self._config.timeout_seconds)
        )
        if self._config.environment in available:
            self._environment_validated = True
            return
        close = difflib.get_close_matches(self._config.environment, available, n=1)
        hint = f" Did you mean {close[0]!r}?" if close else ""
        raise AxleServiceError(
            f"Axle environment {self._config.environment!r} is not served by the "
            f"Axle API (available: {', '.join(available)}).{hint} "
            "Fix 'axle.environment' in axbt_project.yml."
        )

    async def check(self, content: str, *, context: str = "", **kwargs: Any) -> CheckResponse:
        """Evaluate Lean code for errors (plan: lightweight typechecking)."""
        try:
            return await self.client.check(
                content=content,
                environment=await self.resolve_environment(),
                timeout_seconds=self._config.timeout_seconds,
                global_options=dict(self._config.global_options),
                **kwargs,
            )
        except AxleError as exc:
            raise AxleServiceError(
                describe_axle_error(exc, self._config, context)
            ) from exc

    async def verify_proof(
        self,
        formal_statement: str,
        content: str,
        *,
        context: str = "",
        **kwargs: Any,
    ) -> VerifyProofResponse:
        """Verify a proof against a formal statement (kernel-level)."""
        try:
            return await self.client.verify_proof(
                formal_statement=formal_statement,
                content=content,
                environment=await self.resolve_environment(),
                timeout_seconds=self._config.timeout_seconds,
                global_options=dict(self._config.global_options),
                **kwargs,
            )
        except AxleError as exc:
            raise AxleServiceError(
                describe_axle_error(exc, self._config, context)
            ) from exc

    async def share_link(self, request_id: str, *, kind: str = "check") -> str:
        """Mint a share link for a previously served request.

        The platform's share route lives outside the versioned `api/v1`
        surface the SDK wraps, and answers 201 — which the SDK's own
        `_call` rejects as an error — so the POST goes through the
        client's session directly, reusing its auth headers and
        connection pool. The API only accepts ids of requests it has
        actually served (it keeps its own log); the caller is expected
        to treat failures as a warning, not a run failure.

        `kind` selects the web route the link opens: `check` for
        typecheck runs and `verify` for kernel-level runs (the stored
        request itself knows what was served; the route only steers the
        web UI).
        """
        url = f"{self.client.url}/v1/shared-links"
        session = self.client._session
        if session is None or session.closed:
            session = self.client._get_session()
            self.client._session = session
        try:
            async with session.post(url, json={"request_id": request_id}) as resp:
                body = await resp.text()
                if resp.status not in (200, 201):
                    raise AxleServiceError(
                        f"the API could not share this run "
                        f"(HTTP {resp.status}): {body.strip()[:200]}"
                    )
        except aiohttp.ClientError as exc:
            raise AxleServiceError(f"the share request failed: {exc}") from exc
        return f"{self.client.url}/{kind}#r={request_id}"

    async def theorem2sorry(
        self, content: str, *, context: str = "", **kwargs: Any
    ) -> Theorem2SorryResponse:
        """Replace theorem proofs with `sorry` (verify's formal statements).

        The transform preserves everything else — import lines, local
        definitions, order — so the result elaborates standalone even
        when the verified statements reference file-local declarations.
        As with extraction, `ignore_imports=False` is forced: axbt's
        payloads carry their own (hoisted) import lines.
        """
        try:
            return await self.client.theorem2sorry(
                content=content,
                environment=await self.resolve_environment(),
                timeout_seconds=self._config.timeout_seconds,
                global_options=dict(self._config.global_options),
                ignore_imports=False,
                **kwargs,
            )
        except AxleError as exc:
            raise AxleServiceError(
                describe_axle_error(exc, self._config, context)
            ) from exc

    async def extract_decls(
        self, content: str, *, context: str = "", **kwargs: Any
    ) -> ExtractDeclsResponse:
        """Extract per-declaration metadata from Lean code.

        `ignore_imports=False` is forced: axbt's payloads carry their own
        (hoisted) import lines, and letting the API replace them with its
        default header would both change what is evaluated and shift the
        reported line positions.
        """
        try:
            return await self.client.extract_decls(
                content=content,
                environment=await self.resolve_environment(),
                timeout_seconds=self._config.timeout_seconds,
                global_options=dict(self._config.global_options),
                ignore_imports=False,
                **kwargs,
            )
        except AxleError as exc:
            raise AxleServiceError(
                describe_axle_error(exc, self._config, context)
            ) from exc

    async def environments(self, **kwargs: Any) -> list[dict[str, Any]]:
        """List the Lean environments the Axle API serves."""
        try:
            return await self.client.environments(**kwargs)
        except AxleError as exc:
            raise AxleServiceError(
                describe_axle_error(exc, self._config, context="environments")
            ) from exc

    async def close(self) -> None:
        if self._client is not None and hasattr(self._client, "close"):
            await self._client.close()

    async def __aenter__(self) -> "AxleService":
        return self

    async def __aexit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        await self.close()
