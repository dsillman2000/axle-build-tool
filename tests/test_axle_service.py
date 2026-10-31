"""Unit tests for the `axiom-axle` service layer (all offline via fakes)."""

from __future__ import annotations

import asyncio
from typing import Any

import pytest
from axle.exceptions import (
    AxleApiError,
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
    Messages,
    VerifyProofResponse,
)

from axle_build_tool.axle_service import AxleService, AxleServiceError, describe_axle_error
from axle_build_tool.config import AxleConfig, FALLBACK_ENVIRONMENT

CONFIG = AxleConfig(
    environment="lean-4.35.0",
    timeout_seconds=30,
    global_options={"maxHeartbeats": 100000},
)


def make_response(cls: type, **overrides: Any):
    defaults: dict[str, Any] = dict(
        okay=True,
        content="",
        lean_messages=Messages([], [], []),
        tool_messages=Messages([], [], []),
        failed_declarations=[],
        timings={},
        info=None,
    )
    defaults.update(overrides)
    return cls(**defaults)


class FakeAxleClient:
    """Records call kwargs; returns canned results or raises a canned error.

    `error` is raised by the operations; `ping_error` by the
    environment auto-detection endpoint; `latest` is what
    `get_latest_environment` returns when no error is set.
    """

    def __init__(
        self,
        error: Exception | None = None,
        ping_error: Exception | None = None,
        latest: dict[str, Any] | None = None,
    ) -> None:
        self.calls: list[tuple[str, dict[str, Any]]] = []
        self.closed = False
        self._error = error
        self._ping_error = ping_error
        self._latest = latest
        self.check_result = make_response(CheckResponse)
        self.verify_result = make_response(VerifyProofResponse, negation=None)
        self.extract_result = ExtractDeclsResponse(
            content="",
            lean_messages=Messages([], [], []),
            tool_messages=Messages([], [], []),
            documents={},
            timings={},
            info=None,
        )

    async def get_latest_environment(self, **kwargs: Any) -> dict[str, Any] | None:
        self.calls.append(("get_latest_environment", kwargs))
        if self._ping_error:
            raise self._ping_error
        return self._latest

    async def check(self, **kwargs: Any) -> CheckResponse:
        self.calls.append(("check", kwargs))
        if self._error:
            raise self._error
        return self.check_result

    async def verify_proof(self, **kwargs: Any) -> VerifyProofResponse:
        self.calls.append(("verify_proof", kwargs))
        if self._error:
            raise self._error
        return self.verify_result

    async def extract_decls(self, **kwargs: Any) -> ExtractDeclsResponse:
        self.calls.append(("extract_decls", kwargs))
        if self._error:
            raise self._error
        return self.extract_result

    async def environments(self, **kwargs: Any) -> list[dict[str, Any]]:
        self.calls.append(("environments", kwargs))
        if self._error:
            raise self._error
        return [{"name": "lean-4.35.0"}]

    async def close(self) -> None:
        self.closed = True


def make_service(error: Exception | None = None) -> tuple[AxleService, FakeAxleClient]:
    fake = FakeAxleClient(error=error)
    service = AxleService(CONFIG, client_factory=lambda: fake)
    return service, fake


def make_auto_service(fake: FakeAxleClient) -> AxleService:
    """A service with no pinned environment (the default configuration)."""
    return AxleService(AxleConfig(), client_factory=lambda: fake)


def run(coro):
    return asyncio.run(coro)


class TestConfigPlumbing:
    def test_check_applies_project_axle_config(self) -> None:
        service, fake = make_service()
        run(service.check("theorem t : True := True.intro"))
        (method, kwargs) = fake.calls[0]
        assert method == "check"
        assert kwargs["environment"] == "lean-4.35.0"
        assert kwargs["timeout_seconds"] == 30
        assert kwargs["global_options"] == {"maxHeartbeats": 100000}

    def test_verify_proof_applies_project_axle_config(self) -> None:
        service, fake = make_service()
        run(service.verify_proof("theorem t : True := by sorry", "theorem t : True := True.intro"))
        (method, kwargs) = fake.calls[0]
        assert method == "verify_proof"
        assert kwargs["formal_statement"] == "theorem t : True := by sorry"
        assert kwargs["environment"] == "lean-4.35.0"
        assert kwargs["timeout_seconds"] == 30
        assert kwargs["global_options"] == {"maxHeartbeats": 100000}

    def test_extract_decls_applies_project_axle_config(self) -> None:
        service, fake = make_service()
        run(service.extract_decls("def x := 1"))
        (method, kwargs) = fake.calls[0]
        assert method == "extract_decls"
        assert kwargs["environment"] == "lean-4.35.0"
        assert kwargs["timeout_seconds"] == 30
        assert kwargs["global_options"] == {"maxHeartbeats": 100000}

    def test_extra_kwargs_are_forwarded(self) -> None:
        service, fake = make_service()
        run(service.check("code", theorems_only=True, names=["t"]))
        (_, kwargs) = fake.calls[0]
        assert kwargs["theorems_only"] is True
        assert kwargs["names"] == ["t"]

    def test_client_factory_is_used(self) -> None:
        service, fake = make_service()
        assert service.client is fake

    def test_async_context_manager_closes_client(self) -> None:
        fake = FakeAxleClient()
        service = AxleService(CONFIG, client_factory=lambda: fake)

        async def exercise() -> None:
            async with service:
                _ = service.client

        run(exercise())
        assert fake.closed

    def test_environments_passthrough(self) -> None:
        service, fake = make_service()
        result = run(service.environments())
        assert result == [{"name": "lean-4.35.0"}]
        assert [method for method, _ in fake.calls] == ["environments"]


ERROR_CASES = [
    (AxleIsUnavailable("https://axle.axiommath.ai", "connection refused"), "unreachable"),
    (AxleForbiddenError("403"), "AXLE_API_KEY"),
    (AxleRateLimitedError("429"), "rate limit"),
    (LeanTimeout("timed out"), "axle.timeout_seconds"),
    (LeanResourceExceeded("heartbeats"), "global_options"),
    (AxleInvalidArgument("bad request"), "invalid"),
    (AxleApiError("500"), "Axle API error"),
]


class TestErrorMapping:
    @pytest.mark.parametrize("exc,fragment", ERROR_CASES)
    def test_each_axle_error_gets_distinct_guidance(
        self, exc: AxleError, fragment: str
    ) -> None:
        message = describe_axle_error(exc, CONFIG, "")
        assert fragment in message, message

    @pytest.mark.parametrize("exc,_", ERROR_CASES, ids=[type(e).__name__ for e, _ in ERROR_CASES])
    def test_service_wraps_errors_from_any_operation(
        self, exc: AxleError, _: str
    ) -> None:
        for operation in ("check", "verify_proof", "extract_decls"):
            service, fake = make_service(error=exc)
            fake._error = exc
            with pytest.raises(AxleServiceError) as excinfo:
                if operation == "check":
                    run(service.check("code"))
                elif operation == "verify_proof":
                    run(service.verify_proof("stmt", "code"))
                else:
                    run(service.extract_decls("code"))
            assert excinfo.value.__cause__ is exc

    def test_timeout_message_mentions_configured_timeout(self) -> None:
        message = describe_axle_error(LeanTimeout("timed out"), CONFIG, "")
        assert "30" in message

    def test_context_is_prefixed(self) -> None:
        message = describe_axle_error(
            AxleForbiddenError("403"), CONFIG, "checking RootTwoIrrational.Divisibility"
        )
        assert message.startswith("checking RootTwoIrrational.Divisibility: ")

    def test_non_axle_errors_are_not_wrapped(self) -> None:
        service, _ = make_service()
        service._client = object()  # no check method at all

        with pytest.raises(AttributeError):
            run(service.check("code"))


class TestAutoEnvironment:
    """The default configuration has no pinned environment: axbt pings the
    environments endpoint and picks the latest Lean version, falling back
    to lean-4.35.0 only when the Axle API is unreachable."""

    def test_pings_environments_and_picks_latest(self) -> None:
        fake = FakeAxleClient(latest={"name": "lean-4.36.0"})
        service = make_auto_service(fake)

        run(service.check("code"))

        assert [method for method, _ in fake.calls] == [
            "get_latest_environment",
            "check",
        ]
        assert fake.calls[-1][1]["environment"] == "lean-4.36.0"

    def test_latest_result_is_cached_across_operations(self) -> None:
        fake = FakeAxleClient(latest={"name": "lean-4.36.0"})
        service = make_auto_service(fake)

        run(service.check("a"))
        run(service.verify_proof("stmt", "a"))
        run(service.extract_decls("a"))

        pings = [method for method, _ in fake.calls].count("get_latest_environment")
        assert pings == 1
        assert {kwargs["environment"] for _, kwargs in fake.calls[1:]} == {"lean-4.36.0"}

    def test_pings_use_the_configured_timeout(self) -> None:
        fake = FakeAxleClient(latest={"name": "lean-4.36.0"})
        service = AxleService(
            AxleConfig(environment=None, timeout_seconds=77),
            client_factory=lambda: fake,
        )

        run(service.check("code"))

        (_, ping_kwargs) = fake.calls[0]
        assert ping_kwargs["timeout_seconds"] == 77

    def test_unreachable_api_falls_back_to_lean_4_35_0(self) -> None:
        fake = FakeAxleClient(
            ping_error=AxleIsUnavailable("https://axle.axiommath.ai", "connection refused")
        )
        service = make_auto_service(fake)

        run(service.check("code"))

        assert fake.calls[-1][1]["environment"] == FALLBACK_ENVIRONMENT

    def test_fallback_is_cached_no_repeated_pings(self) -> None:
        fake = FakeAxleClient(
            ping_error=AxleIsUnavailable("https://axle.axiommath.ai", "connection refused")
        )
        service = make_auto_service(fake)

        run(service.check("a"))
        run(service.extract_decls("b"))

        pings = [method for method, _ in fake.calls].count("get_latest_environment")
        assert pings == 1
        assert {kwargs["environment"] for _, kwargs in fake.calls[1:]} == {
            FALLBACK_ENVIRONMENT
        }

    def test_no_lean_environments_listed_falls_back(self) -> None:
        fake = FakeAxleClient(latest=None)
        service = make_auto_service(fake)

        run(service.check("code"))

        assert fake.calls[-1][1]["environment"] == FALLBACK_ENVIRONMENT

    def test_explicit_environment_never_pings(self) -> None:
        fake = FakeAxleClient(latest={"name": "lean-4.36.0"})
        service = AxleService(
            AxleConfig(environment="lean-4.99.0"), client_factory=lambda: fake
        )

        run(service.check("code"))

        assert "get_latest_environment" not in [method for method, _ in fake.calls]
        assert fake.calls[0][1]["environment"] == "lean-4.99.0"

    def test_other_detection_errors_are_not_swallowed(self) -> None:
        fake = FakeAxleClient(ping_error=AxleRateLimitedError("429"))
        service = make_auto_service(fake)

        with pytest.raises(AxleServiceError) as excinfo:
            run(service.check("code"))

        assert "rate limit" in str(excinfo.value)
        # No check was submitted with a silently-downgraded environment.
        assert [method for method, _ in fake.calls] == ["get_latest_environment"]
