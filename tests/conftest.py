"""Shared fixtures and paths for the axbt test suite.

The offline suite builds its own throwaway projects; the live suite
(`tests/test_live.py`) builds ad-hoc Lean projects per test. Neither
depends on the repository's `demos/`.
"""

from __future__ import annotations

import asyncio
import dataclasses
import json as jsonlib
import re
from pathlib import Path
from typing import Any

import pytest

from axle.types import (
    CheckResponse,
    Document,
    ExtractDeclsResponse,
    Messages,
    Theorem2SorryResponse,
    VerifyProofResponse,
)


@pytest.fixture
def make_project():
    """Factory for throwaway axbt projects used as test fixtures.

    Writes `axbt_project.yml` with `config_text` and creates each file in
    `files` (relative to the project root, parent dirs included).
    """
    from axle_build_tool.config import CONFIG_FILENAME

    def _make(root: Path, config_text: str, files: dict[str, str]) -> Path:
        root.mkdir(parents=True, exist_ok=True)
        (root / CONFIG_FILENAME).write_text(config_text, encoding="utf-8")
        for relative, content in files.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
        return root

    return _make


# --- axiom-axle test fakes -------------------------------------------------


def make_response(cls: type, **overrides: Any):
    """Build a minimal-valid SDK response dataclass of type `cls`."""
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


def with_declarations(manifest, names_by_node: dict[str, list[str]]):
    """Stamp a freshly-built manifest with canned extraction data.

    Selection resolution matches declarations against the *extracted*
    metadata, which only exists after `axbt compile` has run against the
    API; tests stamp representative declarations directly.
    """
    from axle_build_tool.manifest import ExtractedDecl

    return manifest.model_copy(
        update={
            "nodes": [
                node.model_copy(
                    update={
                        "declarations": [
                            ExtractedDecl(
                                name=name,
                                kind="theorem",
                                is_sorry=False,
                                line_pos=index + 1,
                                end_line_pos=index + 2,
                                signature=f"theorem {name}",
                            )
                            for index, name in enumerate(
                                names_by_node.get(node.name, [])
                            )
                        ]
                    }
                )
                for node in manifest.nodes
            ]
        }
    )


def _decl_record(manifest, decl_name: str):
    """The single `ExtractedDecl` whose extracted name is `decl_name`.

    Stamp assertions want the record itself (several tests across the
    check/verify suites unwind it the same way), so this lives here —
    and asserts uniqueness so a name collision is caught loudly.
    """
    matches = [
        d
        for node in manifest.nodes
        for d in node.declarations
        if d.name == decl_name
    ]
    assert len(matches) == 1, (
        f"declaration {decl_name!r} matched {len(matches)} record(s) in the manifest"
    )
    return matches[0]


def checked_stamp_of(manifest, decl_name: str):
    """The manifest record of `decl_name`, for asserting check stamps."""
    return _decl_record(manifest, decl_name)


def verified_stamp_of(manifest, decl_name: str):
    """The manifest record of `decl_name`, for asserting verify stamps."""
    return _decl_record(manifest, decl_name)


def normalized_lines(output: str) -> list[str]:
    """`output` as whitespace-collapsed, non-empty lines.

    Styled/aligned report lines normalize into comparable text, e.g.
    `theorem  prime_gt_one   [line 11]` -> `theorem prime_gt_one [line 11]`.
    """
    return [" ".join(line.split()) for line in output.splitlines() if line.strip()]


_DOCUMENT_COUNTER = re.compile(r"^\[\s*\d+/\d+\] +")
_TIMESTAMP = re.compile(r"^\d{2}:\d{2}:\d{2}\.\d{3} +")
_ITEM_TIMING = re.compile(r" +\d+\.\d{3}s$")
_TIER_TAG = re.compile(r" +\[(?:check|verify)\]$")


def _strip_prefixes(line: str) -> str:
    """A report line minus its timestamp and progress counter."""
    body = _TIMESTAMP.sub("", line, count=1)
    body = _DOCUMENT_COUNTER.sub("", body, count=1)
    return _TIER_TAG.sub("", body, count=1)


def stripped_lines(output: str) -> list[str]:
    """Every non-empty line, timestamp/counter stripped and normalized.

    Test assertions over report content use this so they can match
    lines without fighting the clock or the `[n/m]` bracket prefixes.
    """
    return [
        " ".join(_strip_prefixes(line).split())
        for line in output.splitlines()
        if line.strip()
    ]


def status_line(output: str, label: str) -> str:
    """The check report line for `label`, whitespace-normalized.

    Report lines pad labels so the status column aligns, lead with a
    timestamp and the item-index counter `[n/m]`, and end with the
    item's elapsed time. A selection's START announcement shares its
    label and index with the verdicts, so those lines are skipped here
    (the verdict verb follows the label; the START one says START).
    """
    for line in output.splitlines():
        body = _strip_prefixes(line)
        tokens = body.split()
        if len(tokens) >= 2 and tokens[0].startswith(label) and tokens[1] == "START":
            continue
        if tokens and tokens[0].startswith(label):
            return _ITEM_TIMING.sub("", " ".join(tokens))
    raise AssertionError(f"no report line for {label!r} in:\n{output}")


def start_line(output: str, label: str) -> str:
    """The START announcement line for `label`, prefix-stripped.

    The stripped body is `label START [RUN]` — the counter and the
    timestamp are tested separately through `raw_report_line`.
    """
    for body in stripped_lines(output):
        tokens = body.split()
        if len(tokens) >= 3 and tokens[0].startswith(label) and tokens[1] == "START":
            return body
    raise AssertionError(f"no START line for {label!r} in:\n{output}")


def raw_report_line(output: str, label: str, verb: str) -> tuple[str, str]:
    """The (raw) report line for `label` whose status verb is `verb`.

    Returns the line's timestamp and `[n/m]` counter, so tests can pin
    the pairing/format themselves (millisecond clock, item-indexed
    counters shared by a selection's START and its verdicts).
    """
    for line in output.splitlines():
        if not _TIMESTAMP.match(line):
            continue
        tokens = line.split()
        if (
            len(tokens) >= 4
            and tokens[2].startswith(label)
            and tokens[3] == verb.upper()
        ):
            return tokens[0], tokens[1]
    raise AssertionError(f"no {verb} line for {label!r} in:\n{output}")


def make_extract_response(
    documents: dict[str, Document], info: dict[str, Any] | None = None
) -> ExtractDeclsResponse:
    """Build an `ExtractDeclsResponse` carrying the given documents."""
    return ExtractDeclsResponse(
        content="",
        lean_messages=Messages([], [], []),
        tool_messages=Messages([], [], []),
        documents=documents,
        timings={},
        info=info,
    )


def make_document(
    name: str = "sample_decl",
    kind: str = "theorem",
    is_sorry: bool = False,
    line_pos: int = 1,
    end_line_pos: int = 2,
    signature: str = "theorem sample_decl : True",
    *,
    local_type_dependencies: list[str] | None = None,
    local_value_dependencies: list[str] | None = None,
    external_type_dependencies: list[str] | None = None,
    external_value_dependencies: list[str] | None = None,
    local_syntactic_dependencies: list[str] | None = None,
    external_syntactic_dependencies: list[str] | None = None,
) -> Document:
    """Build a `Document` with all fields the SDK response type requires.

    The dependency lists default to empty; pass them to model what the
    API reports for declarations that reference other declarations.
    """
    return Document(
        name=name,
        kind=kind,
        declaration=f"theorem {name} : True := by sorry",
        content="",
        tokens=[],
        signature=signature,
        type="True",
        type_hash=None,
        unfolded_type_hash=None,
        type_depth=0,
        term_depth=0,
        is_sorry=is_sorry,
        index=0,
        line_pos=line_pos,
        end_line_pos=end_line_pos,
        proof_length=0,
        tactic_counts={},
        wall_ms=0,
        heartbeats=0,
        local_type_dependencies=local_type_dependencies or [],
        local_value_dependencies=local_value_dependencies or [],
        external_type_dependencies=external_type_dependencies or [],
        external_value_dependencies=external_value_dependencies or [],
        local_syntactic_dependencies=local_syntactic_dependencies or [],
        external_syntactic_dependencies=external_syntactic_dependencies or [],
        declaration_messages=Messages([], [], []),
        theorem_messages=Messages([], [], []),
    )


class _FakeShareResponse:
    def __init__(self, status: int, body: str) -> None:
        self.status = status
        self._body = body

    async def text(self) -> str:
        return self._body


class _FakeSharePost:
    """Async context manager standing in for the POST response."""

    def __init__(self, status: int, body: str) -> None:
        self._response = _FakeShareResponse(status, body)

    async def __aenter__(self) -> _FakeShareResponse:
        return self._response

    async def __aexit__(self, *exc: Any) -> bool:
        return False


class _FakeShareSession:
    """Session stand-in that records share mints.

    `FakeAxleClient.share_status` decides the outcome: an int status
    (201 mints, anything else fails), an exception to raise from the
    POST itself (a network-level failure), or a queue of either for
    multi-POST scenarios (an exhausted queue mints).
    """

    def __init__(self, client: FakeAxleClient) -> None:
        self._client = client
        self.closed = False

    def post(self, url: str, json: dict[str, Any] | None = None) -> _FakeSharePost:
        request_id = (json or {}).get("request_id", "")
        self._client.share_requests.append((url, request_id))
        status = self._client.share_status
        if isinstance(status, list):
            # Queue of per-POST outcomes; an exhausted queue mints.
            status = status.pop(0) if status else 201
        if isinstance(status, Exception):
            raise status
        return _FakeSharePost(
            status, jsonlib.dumps({"request_id": request_id, "saved_at": "now"})
        )


class FakeAxleClient:
    """Offline stand-in for `AxleClient`.

    Records every call's kwargs in `calls` as (method, kwargs) tuples.
    `error` is raised by the operations; `ping_error` by the environment
    auto-detection endpoint; `latest` is what `get_latest_environment`
    returns when no ping error is set. `extract_documents` is returned by
    every `extract_decls` call; `extract_documents_by_marker` routes on a
    substring of the submitted content for per-file fidelity.
    """

    max_concurrency = 3

    def __init__(
        self,
        error: Exception | None = None,
        ping_error: Exception | None = None,
        latest: dict[str, Any] | None = None,
        extract_documents: dict[str, Document] | None = None,
        extract_documents_by_marker: dict[str, dict[str, Document]] | None = None,
        extract_lean_errors: list[str] | None = None,
        environments: list[dict[str, Any]] | None = None,
    ) -> None:
        self.calls: list[tuple[str, dict[str, Any]]] = []
        self.closed = False
        self._error = error
        self._ping_error = ping_error
        self._latest = latest
        self._extract_documents = extract_documents if extract_documents is not None else {
            "sample_decl": make_document()
        }
        self._extract_documents_by_marker = extract_documents_by_marker or {}
        self.check_result = make_response(CheckResponse)
        self.verify_result = make_response(VerifyProofResponse, negation=None)
        #: Content markers whose payloads are failed by `check` (routing
        #: like `check_delays`: a set of substrings; when any occurs in
        #: the submitted content the call's response is okay=False).
        self.check_failures: set[str] = set()
        #: Artificial per-submission delays, letting tests control the
        #: order submissions complete in (and so the streaming report's
        #: completion-order lines). Keyed by a content marker, routed to
        #: whichever payload contains the marker latest — the target's
        #: own file is inlined last.
        self.check_delays: dict[str, float] = {}
        self.verify_delays: dict[str, float] = {}
        self._extract_lean_errors = list(extract_lean_errors or [])
        self._environments = (
            environments if environments is not None else [{"name": "lean-4.35.0"}]
        )
        self._request_counter = 0
        self.request_ids: list[str] = []
        self.url = "https://axle.test"
        #: Share-mint outcome: an HTTP status (201 mints), an exception
        #: raised from the POST itself, or a queue of either for
        #: multi-POST scenarios (an exhausted queue mints).
        self.share_status: int | Exception | list[int | Exception] = 201
        self.share_requests: list[tuple[str, str]] = []
        self._session: _FakeShareSession | None = None

    def _get_session(self) -> _FakeShareSession:
        self._session = _FakeShareSession(self)
        return self._session

    def _with_request_id(self, response: Any) -> Any:
        """A copy of the canned response carrying this call's request id.

        The real API stamps every response with one; `--share` keys
        off it the same way it keys off extraction provenance.
        """
        self._request_counter += 1
        request_id = f"fake-req-{self._request_counter:04d}"
        self.request_ids.append(request_id)
        return dataclasses.replace(
            response,
            info={"request_id": request_id, "environment": "lean-4.35.0"},
        )

    async def get_latest_environment(self, **kwargs: Any) -> dict[str, Any] | None:
        self.calls.append(("get_latest_environment", kwargs))
        if self._ping_error:
            raise self._ping_error
        return self._latest

    @staticmethod
    def _delay_for(delays: dict[str, float], content: str) -> float:
        """The delay routed to a payload by its latest-occurring marker."""
        best_position, delay = -1, 0.0
        for marker, value in delays.items():
            position = content.rfind(marker)
            if position > best_position:
                best_position, delay = position, value
        return delay

    async def check(self, **kwargs: Any) -> CheckResponse:
        self.calls.append(("check", kwargs))
        if self._error:
            raise self._error
        content = kwargs.get("content", "")
        delay = self._delay_for(self.check_delays, content)
        if delay:
            await asyncio.sleep(delay)
        if self.check_failures and any(marker in content for marker in self.check_failures):
            return self._with_request_id(dataclasses.replace(self.check_result, okay=False))
        return self._with_request_id(self.check_result)

    async def verify_proof(self, **kwargs: Any) -> VerifyProofResponse:
        self.calls.append(("verify_proof", kwargs))
        if self._error:
            raise self._error
        delay = self._delay_for(self.verify_delays, kwargs.get("content", ""))
        if delay:
            await asyncio.sleep(delay)
        return self._with_request_id(self.verify_result)

    async def theorem2sorry(self, **kwargs: Any) -> Theorem2SorryResponse:
        self.calls.append(("theorem2sorry", kwargs))
        if self._error:
            raise self._error
        # Echo the requested scope back in the formal statement so tests
        # can assert the names plumbing reached the API.
        names = kwargs.get("names")
        scope = ",".join(names) if names else "all"
        return Theorem2SorryResponse(
            lean_messages=Messages([], [], []),
            tool_messages=Messages([], [], []),
            content=f"formal[{scope}]",
            timings={},
            info=None,
        )

    async def extract_decls(self, **kwargs: Any) -> ExtractDeclsResponse:
        self.calls.append(("extract_decls", kwargs))
        if self._error:
            raise self._error
        content = kwargs.get("content", "")
        # The target's own file is inlined last in a payload, so route on
        # the marker that occurs latest in the content.
        documents = self._extract_documents
        best_position = -1
        for marker, marker_documents in self._extract_documents_by_marker.items():
            position = content.rfind(marker)
            if position > best_position:
                best_position = position
                documents = marker_documents
        self._request_counter += 1
        request_id = f"fake-req-{self._request_counter:04d}"
        self.request_ids.append(request_id)
        response = make_extract_response(
            documents, info={"request_id": request_id, "environment": "lean-4.35.0"}
        )
        response.lean_messages.errors.extend(self._extract_lean_errors)
        return response

    async def environments(self, **kwargs: Any) -> list[dict[str, Any]]:
        self.calls.append(("environments", kwargs))
        if self._error:
            raise self._error
        return self._environments

    async def close(self) -> None:
        self.closed = True


@pytest.fixture
def fake_axle(monkeypatch):
    """Wire a fresh `FakeAxleClient` into the CLI's service seam.

    Tests get the fake back to tweak errors, inspect call counts, or
    route canned extraction results.
    """
    import axle_build_tool.cli as cli
    from axle_build_tool.axle_service import AxleService

    fake = FakeAxleClient()
    monkeypatch.setattr(
        cli, "make_axle_service", lambda config: AxleService(config, client_factory=lambda: fake)
    )
    return fake
