"""The `axbt` command-line interface.

Command-line mechanics are implemented with `click`. The CLI currently
ships a single subcommand, `axbt init [PATH]`; build and verification
commands (`compile` / `check` / `verify`) will follow.
"""

from __future__ import annotations

from collections import Counter
from pathlib import Path

import click

from axle_build_tool.config import CONFIG_FILENAME, ConfigError, load_config, scaffold_config
from axle_build_tool.manifest import (
    ManifestError,
    build_manifest,
    check_targets,
    load_manifest,
    save_manifest,
)
from axle_build_tool.scanner import ScanError

_PLACEHOLDER_SOURCE = """\
/-!
# {module}

Starter module created by `axbt init`. Replace this sample with your own
Lean development.
-/

/-- A trivial sample declaration to get you started. -/
theorem hello_axbt : True := True.intro
"""


@click.group()
@click.version_option(package_name="axle-build-tool", prog_name="axbt")
def main() -> None:
    """axbt — the Axle Build Tool for Lean 4 projects."""


@main.command()
@click.argument(
    "path",
    type=click.Path(path_type=Path),
    required=False,
    default=".",
)
def init(path: Path) -> None:
    """Initialize a new axbt project at PATH (default: current directory)."""
    target = path.resolve()
    config_path = target / CONFIG_FILENAME

    if config_path.exists():
        raise click.ClickException(
            f"{CONFIG_FILENAME} already exists in {target}; "
            "refusing to overwrite an existing axbt project."
        )

    project_name = target.name
    if not project_name:
        raise click.ClickException(
            f"Cannot derive a project name from {target}; "
            "please pass an explicit PATH."
        )

    target.mkdir(parents=True, exist_ok=True)
    config_path.write_text(scaffold_config(project_name), encoding="utf-8")

    module_dir = target / project_name
    module_dir.mkdir(parents=True, exist_ok=True)
    source_file = module_dir / f"{project_name}.lean"
    source_file.write_text(
        _PLACEHOLDER_SOURCE.format(module=project_name),
        encoding="utf-8",
    )

    click.echo(f"Initialized axbt project '{project_name}' in {target}")
    click.echo(f"  Created {CONFIG_FILENAME}")
    click.echo(f"  Created {project_name}/{project_name}.lean")


@main.command()
def compile() -> None:
    """Scan modules, parse imports, and write .axbt/manifest.json."""
    project_root = Path.cwd()

    try:
        config = load_config(project_root)
        try:
            # A missing or damaged manifest simply means we start fresh.
            previous = load_manifest(project_root)
        except ManifestError:
            previous = None
        manifest = build_manifest(project_root, config, previous)
        check_targets(config, manifest)
        written = save_manifest(manifest, project_root)
    except (ConfigError, ScanError, ManifestError) as exc:
        raise click.ClickException(str(exc)) from exc

    counts = Counter(node.status for node in manifest.nodes)
    click.echo(
        f"Compiled {len(manifest.nodes)} file(s) across {len(config.modules)} "
        f"module(s): {counts.get('new', 0)} new, {counts.get('changed', 0)} changed, "
        f"{counts.get('clean', 0)} clean"
    )
    represented = {node.module for node in manifest.nodes}
    for module_name in config.modules:
        if module_name not in represented:
            click.echo(f"  Note: module '{module_name}' has no .lean files")
    click.echo(f"Wrote {written}")
