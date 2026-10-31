"""Shared fixtures and paths for the axbt test suite."""

from __future__ import annotations

from pathlib import Path

import pytest

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
