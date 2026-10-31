"""File-system scanning of module source directories.

A pure function that lists the `.lean` files of a resolved module
directory. Import parsing and dependency tracking are not this module's
concern; they build on the file list it produces.
"""

from __future__ import annotations

from pathlib import Path

#: Suffix of Lean source files.
LEAN_SUFFIX = ".lean"


class ScanError(Exception):
    """Raised when a module source directory cannot be scanned."""


def is_ignored(name: str) -> bool:
    """Return whether a file or directory name should be skipped.

    Hidden entries (dot-prefixed names such as `.axbt`, `.git`, `.venv`, …)
    are always ignored.
    """
    return name.startswith(".")


def _walk(dir_path: Path) -> list[Path]:
    """Recursively collect `.lean` paths relative to `dir_path` (unsorted)."""
    found: list[Path] = []
    for entry in dir_path.iterdir():
        if is_ignored(entry.name):
            continue
        if entry.is_dir():
            for nested in _walk(entry):
                found.append(Path(entry.name) / nested)
        elif entry.is_file() and entry.suffix == LEAN_SUFFIX:
            found.append(Path(entry.name))
    return found


def scan_module(module_dir: Path) -> list[Path]:
    """Recursively list the `.lean` files of `module_dir`.

    Returns a lexicographically sorted list of paths relative to
    `module_dir`, ignoring hidden files/directories and anything that is
    not a `.lean` file.
    """
    if not module_dir.is_dir():
        raise ScanError(f"Module source directory does not exist: {module_dir}")
    return sorted(_walk(module_dir))
