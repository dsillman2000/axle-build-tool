"""Shared fixtures and paths for the axbt test suite."""

from __future__ import annotations

import asyncio
from pathlib import Path
from typing import Any

import pytest
from axle.types import (
    CheckResponse,
    Document,
    ExtractDeclsResponse,
    Messages,
    VerifyProofResponse,
)

#: Repository root, derived from this file's location:
#: tests/conftest.py -> repo root. Used to locate the `demos/` fixtures
#: regardless of the current working directory.
REPO_ROOT = Path(__file__).parents[1]
DEMOS_DIR = REPO_ROOT / "demos"


@pytest.fixture
def demos_dir() -> Path:
    """Path to the repo's `demos/` directory."""
    return DEMOS_DIR


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


def make_extract_response(documents: dict[str, Document]) -> ExtractDeclsResponse:
    """Build an `ExtractDeclsResponse` carrying the given documents."""
    return ExtractDeclsResponse(
        content="",
        lean_messages=Messages([], [], []),
        tool_messages=Messages([], [], []),
        documents=documents,
        timings={},
        info=None,
    )


def make_document(
    name: str = "sample_decl",
    kind: str = "theorem",
    is_sorry: bool = False,
    line_pos: int = 1,
    end_line_pos: int = 2,
    signature: str = "theorem sample_decl : True",
) -> Document:
    """Build a `Document` with all fields the SDK response type requires."""
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
        local_type_dependencies=[],
        local_value_dependencies=[],
        external_type_dependencies=[],
        external_value_dependencies=[],
        local_syntactic_dependencies=[],
        external_syntactic_dependencies=[],
        declaration_messages=Messages([], [], []),
        theorem_messages=Messages([], [], []),
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
        self._extract_lean_errors = list(extract_lean_errors or [])

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
        response = make_extract_response(documents)
        response.lean_messages.errors.extend(self._extract_lean_errors)
        return response

    async def environments(self, **kwargs: Any) -> list[dict[str, Any]]:
        self.calls.append(("environments", kwargs))
        if self._error:
            raise self._error
        return [{"name": "lean-4.35.0"}]

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
