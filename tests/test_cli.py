"""CLI-level tests for the commands axbt ships.

All tests drive the real CLI entry point (`axle_build_tool.main`, the same
object the `axbt` console script exposes) via click's test runner.
"""

from __future__ import annotations

from pathlib import Path

import yaml
from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.config import (
    CACHE_DIRNAME,
    CONFIG_FILENAME,
    AxleConfig,
    load_config,
)
from conftest import make_document

runner = CliRunner()


class TestHelp:
    def test_help_exits_zero_and_lists_init(self) -> None:
        result = runner.invoke(main, ["--help"])
        assert result.exit_code == 0
        assert "init" in result.output


CONFIG = """\
project:
  name: proj
  version: "1.2.3"
modules:
  M:
    targets:
      - A.t1
axle:
  environment: "lean-4.35.0"
  timeout_seconds: 90
  global_options:
    maxHeartbeats: 100000
"""


class TestDebug:
    """`axbt debug` — key verification + project configuration report."""

    def test_debug_prints_project_configuration(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, CONFIG, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(root)
        monkeypatch.setenv("AXLE_API_KEY", "pk_secret_1234567890")
        fake_axle._extract_documents_by_marker = {
            "def t1 := 1": {
                "t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1)
            }
        }
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["debug"])

        assert result.exit_code == 0, result.output
        assert "proj (v1.2.3)" in result.output
        assert str(root) in result.output
        assert "A.t1" in result.output
        assert "1 scanned" in result.output
        assert "lean-4.35.0 — pinned" in result.output
        assert "90 s" in result.output
        assert "maxHeartbeats=100000" in result.output
        # Cache state, reported from the manifest the ritual wrote.
        assert "version 2" in result.output
        assert "1 (0 clean, 0 changed, 1 new)" in result.output
        assert "1 extracted" in result.output
        # The key is verified (the fake serves the probes) and masked.
        assert "reachable:   yes" in result.output
        assert "key valid:   yes" in result.output

    def test_debug_masks_the_api_key(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        make_project(tmp_path, CONFIG, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("AXLE_API_KEY", "pk_secret_1234567890")

        result = runner.invoke(main, ["debug"])

        assert result.exit_code == 0, result.output
        assert "pk_sec…7890" in result.output
        # The full key never appears.
        assert "pk_secret_1234567890" not in result.output

    def test_debug_missing_key_exits_1_without_api_calls(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        make_project(tmp_path, CONFIG, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(tmp_path)
        monkeypatch.delenv("AXLE_API_KEY", raising=False)

        result = runner.invoke(main, ["debug"])

        assert result.exit_code == 1
        assert "NOT SET" in result.output
        assert "AXLE_API_KEY" in result.output
        assert fake_axle.calls == []

    def test_debug_rejects_an_invalid_key(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        from axle.exceptions import AxleForbiddenError

        make_project(tmp_path, CONFIG, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("AXLE_API_KEY", "pk_bogus")
        fake_axle._error = AxleForbiddenError("403")

        result = runner.invoke(main, ["debug"])

        assert result.exit_code == 1
        assert "reachable:   no" in result.output
        assert "AXLE_API_KEY" in result.output

    def test_debug_reports_an_unreachable_api(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        from axle.exceptions import AxleIsUnavailable

        make_project(tmp_path, CONFIG, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("AXLE_API_KEY", "pk_secret_1234567890")
        fake_axle._error = AxleIsUnavailable("https://axle.axiommath.ai", "down")

        result = runner.invoke(main, ["debug"])

        assert result.exit_code == 1
        assert "unreachable" in result.output

    def test_debug_without_a_project_still_checks_the_key(
        self, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("AXLE_API_KEY", "pk_secret_1234567890")

        result = runner.invoke(main, ["debug"])

        assert result.exit_code == 0, result.output
        assert "No axbt_project.yml" in result.output
        assert "key valid:   yes" in result.output

    def test_debug_shows_the_auto_selected_environment(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        auto_config = CONFIG.replace('  environment: "lean-4.35.0"\n', "")
        make_project(tmp_path, auto_config, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("AXLE_API_KEY", "pk_secret_1234567890")

        result = runner.invoke(main, ["debug"])

        assert result.exit_code == 0, result.output
        assert "auto-select" in result.output
        assert "lean-4.35.0 resolved" in result.output


class TestInit:
    def test_init_creates_project(self, tmp_path: Path) -> None:
        target = tmp_path / "my_lean_project"

        result = runner.invoke(main, ["init", str(target)])

        assert result.exit_code == 0, result.output
        assert (target / CONFIG_FILENAME).is_file()
        module_dir = target / "my_lean_project"
        placeholder = module_dir / "my_lean_project.lean"
        assert placeholder.is_file()
        assert "theorem hello_axbt" in placeholder.read_text(encoding="utf-8")
        # The cache directory is generated by `axbt compile`, never by init.
        assert not (target / CACHE_DIRNAME).exists()
        assert f"Initialized axbt project 'my_lean_project'" in result.output

    def test_init_defaults_to_cwd(self, tmp_path: Path, monkeypatch) -> None:
        monkeypatch.chdir(tmp_path)

        result = runner.invoke(main, ["init"])

        assert result.exit_code == 0, result.output
        assert (tmp_path / CONFIG_FILENAME).is_file()
        assert (tmp_path / tmp_path.name / f"{tmp_path.name}.lean").is_file()

    def test_init_scaffold_round_trips_through_our_loader(
        self, tmp_path: Path
    ) -> None:
        target = tmp_path / "my_lean_project"

        result = runner.invoke(main, ["init", str(target)])
        assert result.exit_code == 0, result.output

        config = load_config(target)  # must parse with axbt's own loader
        assert config.name == "my_lean_project"
        assert config.version == "0.1.0"
        assert set(config.modules) == {"my_lean_project"}
        module = config.modules["my_lean_project"]
        # No `dir` key in the scaffold: the defaulting rule applies.
        assert module.dir == "my_lean_project"
        assert module.targets == ()
        assert config.axle == AxleConfig()
        # And the written YAML is valid YAML for other tooling too.
        raw = yaml.safe_load((target / CONFIG_FILENAME).read_text(encoding="utf-8"))
        assert raw["project"]["name"] == "my_lean_project"

    def test_init_refuses_existing_project(self, tmp_path: Path) -> None:
        target = tmp_path / "my_lean_project"
        first = runner.invoke(main, ["init", str(target)])
        assert first.exit_code == 0, first.output
        original = (target / CONFIG_FILENAME).read_text(encoding="utf-8")

        second = runner.invoke(main, ["init", str(target)])

        assert second.exit_code != 0
        assert "already exists" in second.output
        # The pre-existing project file is left untouched.
        assert (target / CONFIG_FILENAME).read_text(encoding="utf-8") == original
