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
