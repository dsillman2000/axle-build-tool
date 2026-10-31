"""Tests exercising the demo projects under `demos/` as real fixtures.

The demos double as regression fixtures: they are parsed with axbt's real
config loader and scanned with the real scanner.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from axle_build_tool.config import ProjectConfig, load_config
from axle_build_tool.scanner import scan_module

DEMO_NAMES = ("RootTwoIrrational", "GaussIntSum")


def load_demo(demos_dir: Path, name: str) -> tuple[ProjectConfig, Path]:
    """Load a demo project, returning (config, project_root)."""
    root = demos_dir / name
    return load_config(root), root


def test_both_demo_configs_parse(demos_dir: Path) -> None:
    for name in DEMO_NAMES:
        config, _ = load_demo(demos_dir, name)
        assert set(config.modules) == {name}


class TestRootTwoIrrational:
    def test_explicit_dir_is_honored(self, demos_dir: Path) -> None:
        config, _ = load_demo(demos_dir, "RootTwoIrrational")
        module = config.modules["RootTwoIrrational"]
        assert module.dir == "RootTwoIrrational"

    def test_scanner_returns_exact_files_in_sorted_order(
        self, demos_dir: Path
    ) -> None:
        config, root = load_demo(demos_dir, "RootTwoIrrational")
        module_dir = config.module_path(root, "RootTwoIrrational")

        files = scan_module(module_dir)

        assert [str(p) for p in files] == [
            "Divisibility.lean",
            "EuclidLemma.lean",
            "IrrationalSqrtTwo.lean",
        ]


class TestGaussIntSum:
    def test_default_dir_rule_resolves_to_module_name(self, demos_dir: Path) -> None:
        config, _ = load_demo(demos_dir, "GaussIntSum")
        module = config.modules["GaussIntSum"]
        # `dir` is omitted in the demo's axbt_project.yml; it must default
        # to the module's own name.
        assert module.dir == "GaussIntSum"

    def test_scanner_returns_exact_file_via_default_dir(self, demos_dir: Path) -> None:
        config, root = load_demo(demos_dir, "GaussIntSum")
        module_dir = config.module_path(root, "GaussIntSum")

        files = scan_module(module_dir)

        assert [str(p) for p in files] == ["GaussSum.lean"]


@pytest.mark.parametrize("demo_name", DEMO_NAMES)
class TestDemoTargetsResolveToFiles:
    def test_every_target_declaration_appears_in_its_file(
        self, demos_dir: Path, demo_name: str
    ) -> None:
        config, root = load_demo(demos_dir, demo_name)
        (module,) = config.modules.values()
        module_dir = config.module_path(root, module.name)
        scanned = {p.name for p in scan_module(module_dir)}

        assert module.targets, f"demo {demo_name} must declare targets"
        for target in module.targets:
            file_stem, _, declaration = target.partition(".")
            filename = f"{file_stem}.lean"
            assert filename in scanned, (
                f"target {target!r} refers to {filename}, which the scanner "
                f"did not find in {module_dir}"
            )
            content = (module_dir / filename).read_text(encoding="utf-8")
            pattern = rf"\b(?:theorem|def|lemma)\s+{re.escape(declaration)}\b"
            assert re.search(pattern, content), (
                f"declaration {declaration!r} of target {target!r} not found "
                f"in {filename}"
            )
