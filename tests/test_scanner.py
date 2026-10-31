"""Unit tests for the module file-system scanner."""

from __future__ import annotations

from pathlib import Path

import pytest

from axle_build_tool.scanner import ScanError, scan_module


class TestScannerFiltering:
    def test_ignores_hidden_files_hidden_dirs_and_non_lean_files(
        self, tmp_path: Path
    ) -> None:
        # A regular file and a nested one: the only things that should survive.
        (tmp_path / "A.lean").write_text("-- a\n", encoding="utf-8")
        (tmp_path / "sub").mkdir()
        (tmp_path / "sub" / "D.lean").write_text("-- d\n", encoding="utf-8")

        # Planted noise: a hidden file, a hidden dir, and a non-.lean file.
        (tmp_path / ".hidden.lean").write_text("-- hidden file\n", encoding="utf-8")
        (tmp_path / ".axbt").mkdir()
        (tmp_path / ".axbt" / "cached.lean").write_text("-- hidden dir\n", encoding="utf-8")
        (tmp_path / ".git").mkdir()
        (tmp_path / ".git" / "config.lean").write_text("-- hidden dir\n", encoding="utf-8")
        (tmp_path / "notes.txt").write_text("not lean\n", encoding="utf-8")

        result = scan_module(tmp_path)

        assert result == [Path("A.lean"), Path("sub/D.lean")]

    def test_results_are_sorted_and_relative(self, tmp_path: Path) -> None:
        for name in ("C.lean", "A.lean", "B.lean"):
            (tmp_path / name).write_text("--\n", encoding="utf-8")

        result = scan_module(tmp_path)

        assert result == [
            Path("A.lean"),
            Path("B.lean"),
            Path("C.lean"),
        ]
        assert all(not p.is_absolute() for p in result)

    def test_recurses_into_plain_subdirectories(self, tmp_path: Path) -> None:
        (tmp_path / "deep" / "deeper").mkdir(parents=True)
        (tmp_path / "deep" / "deeper" / "X.lean").write_text("--\n", encoding="utf-8")

        assert scan_module(tmp_path) == [Path("deep/deeper/X.lean")]

    def test_missing_module_dir_raises(self, tmp_path: Path) -> None:
        with pytest.raises(ScanError, match="does not exist"):
            scan_module(tmp_path / "nope")
