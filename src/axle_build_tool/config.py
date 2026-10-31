"""Loading, validation, and scaffolding of `axbt_project.yml` files.

The configuration schema is defined in `GEMINI_PLAN.md` §2. The cache
directory `.axbt/` is intentionally **not** part of the schema: it is fixed
and cannot be overridden (see §2, "Notes on configuration behavior").
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import yaml

CONFIG_FILENAME = "axbt_project.yml"

#: The one and only cache directory. Not configurable, by design.
CACHE_DIRNAME = ".axbt"

DEFAULT_ENVIRONMENT = "lean-v4.35.0"
DEFAULT_TIMEOUT_SECONDS = 120

_TOP_LEVEL_KEYS = {"project", "modules", "axle"}
_MODULE_KEYS = {"dir", "targets"}
_AXLE_KEYS = {"environment", "timeout_seconds", "global_options"}
_PROJECT_KEYS = {"name", "version"}

#: Top-level keys left over from the old config shape that most plausibly
#: indicate a typo'd attempt at configuring the (fixed) cache directory.
_CACHE_HINT_KEYS = {"dirs", "cache"}


class ConfigError(Exception):
    """Raised when an `axbt_project.yml` file is missing or invalid."""


@dataclass(frozen=True)
class AxleConfig:
    """Settings for talking to the Axle (Axiom Lean Engine) API."""

    environment: str = DEFAULT_ENVIRONMENT
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS
    global_options: dict[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class ModuleConfig:
    """One module: a named directory of `.lean` files.

    `dir` is stored already defaulted to the module's own name, per §2.
    """

    name: str
    dir: str
    targets: tuple[str, ...] = ()


@dataclass(frozen=True)
class ProjectConfig:
    """A parsed `axbt_project.yml`."""

    modules: dict[str, ModuleConfig]
    axle: AxleConfig = field(default_factory=AxleConfig)
    name: str | None = None
    version: str | None = None

    def module_path(self, project_root: Path, name: str) -> Path:
        """Return the resolved source directory of module `name`."""
        module = self.modules[name]
        return project_root / module.dir


def _is_mapping(value: Any) -> bool:
    return isinstance(value, dict)


def _require_mapping(
    value: Any,
    *,
    where: str,
    message: str | None = None,
) -> dict[str, Any]:
    if value is None:
        return {}
    if not _is_mapping(value):
        raise ConfigError(message or f"{where} must be a mapping, got {_type_name(value)}.")
    return value


def _type_name(value: Any) -> str:
    if value is None:
        return "nothing"
    return type(value).__name__


def _reject_unknown_keys(
    mapping: dict[str, Any],
    *,
    allowed: set[str],
    where: str,
) -> None:
    unknown = set(mapping) - allowed
    if unknown:
        names = ", ".join(repr(key) for key in sorted(unknown, key=str))
        raise ConfigError(
            f"Unknown key(s) {names} in {where}. Allowed keys: "
            f"{', '.join(sorted(allowed))}."
        )


def _top_level_unknown_key_error(unknown: set[Any]) -> ConfigError:
    names = ", ".join(repr(key) for key in sorted(unknown, key=str))
    cache_hints = {str(key) for key in unknown} & _CACHE_HINT_KEYS
    if cache_hints:
        hinted = sorted(cache_hints)[0]
        return ConfigError(
            f"Unknown top-level key {hinted!r} in {CONFIG_FILENAME}: the cache "
            f"directory is fixed at '{CACHE_DIRNAME}/' and cannot be configured. "
            "Module source directories are configured under 'modules' instead."
        )
    return ConfigError(
        f"Unknown top-level key(s) {names} in {CONFIG_FILENAME}. "
        f"Allowed keys: {', '.join(sorted(_TOP_LEVEL_KEYS))}."
    )


def _parse_project(raw: Any) -> tuple[str | None, str | None]:
    project = _require_mapping(
        raw,
        where="'project'",
        message=f"'project' must be a mapping, got {_type_name(raw)}.",
    )
    _reject_unknown_keys(project, allowed=_PROJECT_KEYS, where="'project'")
    name = project.get("name")
    version = project.get("version")
    if name is not None and not isinstance(name, str):
        raise ConfigError(f"'project.name' must be a string, got {_type_name(name)}.")
    if version is not None and not isinstance(version, str):
        raise ConfigError(f"'project.version' must be a string, got {_type_name(version)}.")
    return name, version


def _parse_module(name: Any, raw: Any) -> ModuleConfig:
    if not isinstance(name, str) or not name:
        raise ConfigError(
            f"Module names must be non-empty strings, got {name!r}."
        )
    where = f"module {name!r}"
    if raw is None:
        raw = {}
    if not _is_mapping(raw):
        raise ConfigError(
            f"{where} must be a mapping of settings, got {_type_name(raw)}."
        )
    _reject_unknown_keys(raw, allowed=_MODULE_KEYS, where=where)

    module_dir = raw.get("dir")
    if module_dir is None:
        module_dir = name  # Default: the module's own name (§2).
    elif not isinstance(module_dir, str):
        raise ConfigError(
            f"{where}: 'dir' must be a string, got {_type_name(module_dir)}."
        )

    raw_targets = raw.get("targets")
    if raw_targets is None:
        targets: tuple[str, ...] = ()
    elif isinstance(raw_targets, list) and all(isinstance(t, str) for t in raw_targets):
        targets = tuple(raw_targets)
    else:
        raise ConfigError(
            f"{where}: 'targets' must be a list of strings, "
            f"got {_type_name(raw_targets)}."
        )

    return ModuleConfig(name=name, dir=module_dir, targets=targets)


def _parse_modules(raw: Any) -> dict[str, ModuleConfig]:
    if raw is None:
        raise ConfigError(
            f"{CONFIG_FILENAME} must define a non-empty 'modules' mapping."
        )
    if not _is_mapping(raw):
        raise ConfigError(
            f"'modules' must be a mapping of module name -> module config, "
            f"got {_type_name(raw)}."
        )
    if not raw:
        raise ConfigError("'modules' must contain at least one module.")
    modules = {str(name): _parse_module(name, raw[name]) for name in raw}
    return modules


def _parse_axle(raw: Any) -> AxleConfig:
    axle = _require_mapping(
        raw,
        where="'axle'",
        message=f"'axle' must be a mapping, got {_type_name(raw)}.",
    )
    _reject_unknown_keys(axle, allowed=_AXLE_KEYS, where="'axle'")

    environment = axle.get("environment", DEFAULT_ENVIRONMENT)
    if not isinstance(environment, str):
        raise ConfigError(
            f"'axle.environment' must be a string, got {_type_name(environment)}."
        )

    timeout_seconds = axle.get("timeout_seconds", DEFAULT_TIMEOUT_SECONDS)
    if isinstance(timeout_seconds, bool) or not isinstance(timeout_seconds, int):
        raise ConfigError(
            f"'axle.timeout_seconds' must be an integer, "
            f"got {_type_name(timeout_seconds)}."
        )

    raw_global_options = axle.get("global_options", {})
    if raw_global_options is None:
        raw_global_options = {}
    if not _is_mapping(raw_global_options):
        raise ConfigError(
            f"'axle.global_options' must be a mapping, "
            f"got {_type_name(raw_global_options)}."
        )
    global_options = dict(raw_global_options)
    bad_keys = [key for key in global_options if not isinstance(key, str)]
    if bad_keys:
        raise ConfigError(
            f"'axle.global_options' keys must be strings, got {bad_keys[0]!r}."
        )

    return AxleConfig(
        environment=environment,
        timeout_seconds=timeout_seconds,
        global_options=global_options,
    )


def load_config(project_root: Path) -> ProjectConfig:
    """Load and validate `axbt_project.yml` from `project_root`.

    Raises `ConfigError` with an actionable message if the file is missing
    or invalid.
    """
    config_path = project_root / CONFIG_FILENAME
    if not config_path.is_file():
        raise ConfigError(
            f"No {CONFIG_FILENAME} found in {project_root}. "
            "Run `axbt init` to create a new project."
        )

    try:
        raw = yaml.safe_load(config_path.read_text(encoding="utf-8"))
    except yaml.YAMLError as exc:
        raise ConfigError(f"Could not parse {config_path}: {exc}") from exc

    if raw is None:
        raise ConfigError(f"{config_path} is empty; expected a configuration mapping.")
    if not _is_mapping(raw):
        raise ConfigError(
            f"{config_path} must contain a top-level mapping, "
            f"got {_type_name(raw)}."
        )

    unknown = set(raw) - _TOP_LEVEL_KEYS
    if unknown:
        raise _top_level_unknown_key_error(unknown)

    name, version = _parse_project(raw.get("project"))
    modules = _parse_modules(raw.get("modules"))
    axle = _parse_axle(raw.get("axle"))

    return ProjectConfig(name=name, version=version, modules=modules, axle=axle)


def scaffold_config(project_name: str) -> str:
    """Return the initial `axbt_project.yml` contents for a new project.

    The starter module is named after the project and omits `dir`,
    exercising the default-dir rule (§2). The `axle` section is written out
    with the default values from `AxleConfig`.
    """
    defaults = AxleConfig()
    config: dict[str, Any] = {
        "project": {"name": project_name, "version": "0.1.0"},
        "modules": {project_name: {"targets": []}},
        "axle": {
            "environment": defaults.environment,
            "timeout_seconds": defaults.timeout_seconds,
            "global_options": dict(defaults.global_options),
        },
    }
    return yaml.safe_dump(config, sort_keys=False)
