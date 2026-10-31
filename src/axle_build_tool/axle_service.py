"""Async service layer around the `axiom-axle` SDK.

Owns `AxleClient` construction (the SDK reads `AXLE_API_URL`,
`AXLE_MAX_CONCURRENCY`, `AXLE_TIMEOUT_SECONDS`, and `AXLE_API_KEY` from
the environment itself) and applies the project's `axle` settings
(`environment`, `timeout_seconds`, `global_options`) to every request.
API errors are translated into `AxleServiceError` with actionable,
user-facing messages.

The CLI stays synchronous; command bodies run these coroutines via
`asyncio.run`. Tests inject a fake client through `client_factory`.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

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
from axle.types import CheckResponse, ExtractDeclsResponse, VerifyProofResponse

from axle_build_tool.config import AxleConfig

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

    @property
    def client(self) -> Any:
        if self._client is None:
            self._client = self._client_factory()
        return self._client

    async def check(self, content: str, *, context: str = "", **kwargs: Any) -> CheckResponse:
        """Evaluate Lean code for errors (plan: lightweight typechecking)."""
        try:
            return await self.client.check(
                content=content,
                environment=self._config.environment,
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
                environment=self._config.environment,
                timeout_seconds=self._config.timeout_seconds,
                global_options=dict(self._config.global_options),
                **kwargs,
            )
        except AxleError as exc:
            raise AxleServiceError(
                describe_axle_error(exc, self._config, context)
            ) from exc

    async def extract_decls(
        self, content: str, *, context: str = "", **kwargs: Any
    ) -> ExtractDeclsResponse:
        """Extract per-declaration metadata from Lean code."""
        try:
            return await self.client.extract_decls(
                content=content,
                environment=self._config.environment,
                timeout_seconds=self._config.timeout_seconds,
                global_options=dict(self._config.global_options),
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
