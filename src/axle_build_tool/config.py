"""Loading and validation of `axbt_project.yml` files.

The cache directory `.axbt/` is intentionally **not** part of the schema:
it is fixed and cannot be overridden.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

import yaml
from pydantic import (
    BaseModel,
    ConfigDict,
    Field,
    ValidationError,
    field_validator,
    model_validator,
)

CONFIG_FILENAME = "axbt_project.yml"

#: The one and only cache directory. Not configurable, by design.
CACHE_DIRNAME = ".axbt"

#: The environment used as an ultimate fallback when axbt is asked to pick
#: the latest Lean environment automatically but the Axle API is unreachable.
FALLBACK_ENVIRONMENT = "lean-4.35.0"
DEFAULT_TIMEOUT_SECONDS = 120

#: Top-level keys left over from the old config shape that most plausibly
#: indicate a typo'd attempt at configuring the (fixed) cache directory.
_CACHE_HINT_KEYS = {"dirs", "cache"}


class ConfigError(Exception):
    """Raised when an `axbt_project.yml` file is missing or invalid."""


class AxleConfig(BaseModel):
    """Settings for talking to the Axle (Axiom Lean Engine) API."""

    model_config = ConfigDict(extra="forbid", frozen=True)

    #: Lean environment for API calls. `None` (the default) means auto:
    #: axbt asks the Axle API for its environments and picks the latest
    #: Lean version, falling back to `FALLBACK_ENVIRONMENT` when the API
    #: is unreachable. An explicit value is used verbatim.
    environment: str | None = None
    timeout_seconds: int = Field(default=DEFAULT_TIMEOUT_SECONDS, strict=True)
    #: Lean global options forwarded verbatim to the Axle API.
    global_options: dict[str, bool | int | str] = Field(default_factory=dict)


class ModuleConfig(BaseModel):
    """One module: a named directory of `.lean` files.

    `dir` is stored already defaulted to the module's own name.
    """

    model_config = ConfigDict(extra="forbid", frozen=True)

    name: str
    dir: str = ""
    targets: tuple[str, ...] = ()

    @model_validator(mode="before")
    @classmethod
    def _default_dir(cls, values: Any) -> Any:
        if isinstance(values, dict) and not values.get("dir"):
            values = {**values, "dir": values.get("name")}
        return values


class ProjectConfig(BaseModel):
    """A parsed `axbt_project.yml`."""

    model_config = ConfigDict(frozen=True)

    name: str | None = None
    version: str | None = None
    modules: dict[str, ModuleConfig] = Field(min_length=1)
    axle: AxleConfig = Field(default_factory=AxleConfig)

    def module_path(self, project_root: Path, name: str) -> Path:
        """Return the resolved source directory of module `name`."""
        return project_root / self.modules[name].dir


class _ProjectMeta(BaseModel):
    """The optional `project` metadata section."""

    model_config = ConfigDict(extra="forbid")

    name: str | None = None
    version: str | None = None


class _Document(BaseModel):
    """The top-level `axbt_project.yml` document."""

    model_config = ConfigDict(extra="forbid")

    project: _ProjectMeta = Field(default_factory=_ProjectMeta)
    modules: dict[str, ModuleConfig] = Field(min_length=1)
    axle: AxleConfig = Field(default_factory=AxleConfig)

    @field_validator("modules", mode="before")
    @classmethod
    def _inject_module_names(cls, value: Any) -> Any:
        # In YAML the module name is the mapping key, not a field of the
        # module config; lift it into the model before validation.
        if isinstance(value, dict):
            return {
                key: {"name": key, **cfg} if isinstance(cfg, dict) else cfg
                for key, cfg in value.items()
            }
        return value


def _format_validation_error(exc: ValidationError) -> str:
    lines = []
    for error in exc.errors():
        location = " -> ".join(str(part) for part in error["loc"]) or "document"
        lines.append(f"{location}: {error['msg']}")
    return "; ".join(lines)


def _to_config_error(exc: ValidationError) -> ConfigError:
    for error in exc.errors():
        if error["type"] == "extra_forbidden" and error["loc"]:
            key = str(error["loc"][0])
            if key in _CACHE_HINT_KEYS:
                return ConfigError(
                    f"Unknown top-level key {key!r} in {CONFIG_FILENAME}: the cache "
                    f"directory is fixed at '{CACHE_DIRNAME}/' and cannot be "
                    "configured. Module source directories are configured under "
                    "'modules' instead."
                )
    return ConfigError(
        f"Invalid {CONFIG_FILENAME}: {_format_validation_error(exc)}"
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

    try:
        document = _Document.model_validate(raw)
    except ValidationError as exc:
        raise _to_config_error(exc) from exc

    return ProjectConfig(
        name=document.project.name,
        version=document.project.version,
        modules=document.modules,
        axle=document.axle,
    )


def scaffold_config(project_name: str) -> str:
    """Return the initial `axbt_project.yml` contents for a new project.

    The starter module is named after the project and omits `dir`,
    exercising the default-dir rule. The `axle` section is written out
    with the default values from `AxleConfig`; the environment is left
    out so new projects auto-select the latest Lean environment the Axle
    API offers.
    """
    defaults = AxleConfig()
    axle_section: dict[str, Any] = {
        "timeout_seconds": defaults.timeout_seconds,
        "global_options": dict(defaults.global_options),
    }
    if defaults.environment is not None:
        axle_section = {"environment": defaults.environment, **axle_section}
    config: dict[str, Any] = {
        "project": {"name": project_name, "version": "0.1.0"},
        "modules": {project_name: {"targets": []}},
        "axle": axle_section,
    }
    return yaml.safe_dump(config, sort_keys=False)
