"""Unit tests for the `axbt_project.yml` config loader."""

from __future__ import annotations

from pathlib import Path

import pytest

from axle_build_tool.config import (
    CACHE_DIRNAME,
    CONFIG_FILENAME,
    AxleConfig,
    ConfigError,
    load_config,
)


def write_config(tmp_path: Path, text: str) -> Path:
    (tmp_path / CONFIG_FILENAME).write_text(text, encoding="utf-8")
    return tmp_path


class TestModuleConfig:
    def test_module_dir_defaults_to_module_name(self, tmp_path: Path) -> None:
        write_config(tmp_path, "modules:\n  Foo: {}\n")
        config = load_config(tmp_path)
        assert set(config.modules) == {"Foo"}
        assert config.modules["Foo"].dir == "Foo"
        assert config.modules["Foo"].targets == ()

    def test_explicit_dir_is_honored(self, tmp_path: Path) -> None:
        write_config(tmp_path, "modules:\n  Foo:\n    dir: sources/foo\n")
        config = load_config(tmp_path)
        assert config.modules["Foo"].dir == "sources/foo"

    def test_targets_are_parsed(self, tmp_path: Path) -> None:
        write_config(
            tmp_path,
            "modules:\n  Foo:\n    targets:\n      - Bar.baz\n      - Qux.quux\n",
        )
        config = load_config(tmp_path)
        assert config.modules["Foo"].targets == ("Bar.baz", "Qux.quux")

    def test_modules_is_required(self, tmp_path: Path) -> None:
        write_config(tmp_path, "project:\n  name: foo\n")
        with pytest.raises(ConfigError, match=r"'?modules'?"):
            load_config(tmp_path)

    def test_modules_must_be_non_empty(self, tmp_path: Path) -> None:
        write_config(tmp_path, "modules: {}\n")
        with pytest.raises(ConfigError, match=r"non-empty|at least 1 item"):
            load_config(tmp_path)

    def test_modules_must_be_a_mapping(self, tmp_path: Path) -> None:
        write_config(tmp_path, "modules: [Foo, Bar]\n")
        with pytest.raises(ConfigError, match=r"modules.*dictionary"):
            load_config(tmp_path)

    @pytest.mark.parametrize("bad", ["dir: [a, b]", "dir: 3"])
    def test_module_dir_must_be_a_string(self, tmp_path: Path, bad: str) -> None:
        write_config(tmp_path, f"modules:\n  Foo:\n    {bad}\n")
        with pytest.raises(ConfigError, match=r"modules -> Foo -> dir"):
            load_config(tmp_path)

    @pytest.mark.parametrize("bad", ["targets: Bar.baz", "targets: [1, 2]"])
    def test_targets_must_be_a_list_of_strings(
        self, tmp_path: Path, bad: str
    ) -> None:
        write_config(tmp_path, f"modules:\n  Foo:\n    {bad}\n")
        with pytest.raises(ConfigError, match=r"modules -> Foo -> targets"):
            load_config(tmp_path)


class TestAxleConfig:
    def test_defaults_when_section_omitted(self, tmp_path: Path) -> None:
        write_config(tmp_path, "modules:\n  Foo: {}\n")
        config = load_config(tmp_path)
        assert config.axle == AxleConfig()
        assert config.axle.environment == "lean-v4.35.0"
        assert config.axle.timeout_seconds == 120
        assert config.axle.global_options == {}

    def test_partial_section_keeps_defaults_for_the_rest(self, tmp_path: Path) -> None:
        write_config(
            tmp_path,
            "modules:\n  Foo: {}\naxle:\n  environment: lean-v4.99.0\n",
        )
        config = load_config(tmp_path)
        assert config.axle.environment == "lean-v4.99.0"
        assert config.axle.timeout_seconds == 120
        assert config.axle.global_options == {}

    def test_explicit_values_override_defaults(self, tmp_path: Path) -> None:
        write_config(
            tmp_path,
            "modules:\n  Foo: {}\n"
            "axle:\n"
            "  environment: lean-v4.40.0\n"
            "  timeout_seconds: 30\n"
            "  global_options:\n"
            "    maxHeartbeats: 100000\n",
        )
        config = load_config(tmp_path)
        assert config.axle == AxleConfig(
            environment="lean-v4.40.0",
            timeout_seconds=30,
            global_options={"maxHeartbeats": 100000},
        )

    def test_timeout_seconds_must_be_an_int(self, tmp_path: Path) -> None:
        write_config(
            tmp_path, "modules:\n  Foo: {}\naxle:\n  timeout_seconds: 120s\n"
        )
        with pytest.raises(ConfigError, match=r"axle -> timeout_seconds"):
            load_config(tmp_path)

    def test_timeout_seconds_rejects_bool(self, tmp_path: Path) -> None:
        write_config(tmp_path, "modules:\n  Foo: {}\naxle:\n  timeout_seconds: true\n")
        with pytest.raises(ConfigError, match=r"axle -> timeout_seconds"):
            load_config(tmp_path)

    def test_environment_must_be_a_string(self, tmp_path: Path) -> None:
        write_config(tmp_path, "modules:\n  Foo: {}\naxle:\n  environment: 4.35\n")
        with pytest.raises(ConfigError, match=r"axle -> environment"):
            load_config(tmp_path)


class TestUnknownKeys:
    def test_rejects_leftover_dirs_key(self, tmp_path: Path) -> None:
        write_config(
            tmp_path, "modules:\n  Foo: {}\ndirs:\n  Foo: sources/foo\n"
        )
        with pytest.raises(ConfigError, match=r"'dirs'.*\.axbt/"):
            load_config(tmp_path)

    def test_rejects_leftover_cache_key(self, tmp_path: Path) -> None:
        write_config(
            tmp_path, "modules:\n  Foo: {}\ncache: .cache/axbt\n"
        )
        with pytest.raises(ConfigError, match=r"'cache'.*\.axbt/"):
            load_config(tmp_path)

    def test_cache_hint_mentions_fixed_location(self, tmp_path: Path) -> None:
        write_config(tmp_path, "modules:\n  Foo: {}\ncache: elsewhere\n")
        with pytest.raises(ConfigError) as excinfo:
            load_config(tmp_path)
        assert CACHE_DIRNAME in str(excinfo.value)

    def test_rejects_any_unknown_top_level_key(self, tmp_path: Path) -> None:
        write_config(tmp_path, "modules:\n  Foo: {}\nbogus: true\n")
        with pytest.raises(ConfigError, match=r"bogus.*[Ee]xtra inputs"):
            load_config(tmp_path)


class TestFileHandling:
    def test_missing_config_file(self, tmp_path: Path) -> None:
        with pytest.raises(ConfigError, match=CONFIG_FILENAME):
            load_config(tmp_path)

    def test_malformed_yaml(self, tmp_path: Path) -> None:
        write_config(tmp_path, "modules: [Foo\nmodules: [Bar\n")
        with pytest.raises(ConfigError, match="parse"):
            load_config(tmp_path)

    def test_non_mapping_document(self, tmp_path: Path) -> None:
        write_config(tmp_path, "- just\n- a\n- list\n")
        with pytest.raises(ConfigError, match="dictionary"):
            load_config(tmp_path)

    def test_empty_document(self, tmp_path: Path) -> None:
        write_config(tmp_path, "")
        with pytest.raises(ConfigError, match="empty"):
            load_config(tmp_path)
