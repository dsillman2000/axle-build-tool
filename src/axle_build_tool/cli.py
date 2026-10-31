"""The `axbt` command-line interface.

Command-line mechanics are implemented with `click`. The CLI currently
ships a single subcommand, `axbt init [PATH]`; build and verification
commands (`compile` / `check` / `verify`) will follow.
"""

from __future__ import annotations

import asyncio
from collections import Counter
from pathlib import Path

import click

from axle_build_tool.axle_service import AxleService, AxleServiceError
from axle_build_tool.config import (
    CACHE_DIRNAME,
    CONFIG_FILENAME,
    AxleConfig,
    ConfigError,
    load_config,
    scaffold_config,
)
from axle_build_tool.extraction import ExtractionError, apply_extraction
from axle_build_tool.manifest import (
    MANIFEST_VERSION,
    ManifestError,
    build_manifest,
    check_targets,
    load_manifest,
    save_manifest,
    topological_order,
)
from axle_build_tool.payloads import (
    compiled_payload_dir,
    write_compiled_payloads,
)
from axle_build_tool.scanner import ScanError
from axle_build_tool.selection import SelectionError, resolve_selection

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


def make_axle_service(config: AxleConfig) -> AxleService:
    """Build the Axle service for CLI commands (tests patch this seam)."""
    return AxleService(config)


@main.command()
def compile() -> None:
    """Scan modules, extract declarations via Axle, and write .axbt/manifest.json."""
    project_root = Path.cwd()

    try:
        config = load_config(project_root)
        try:
            # A missing, damaged, or stale-versioned manifest simply means
            # we start fresh (everything gets re-extracted).
            previous = load_manifest(project_root)
            if previous.version != MANIFEST_VERSION:
                previous = None
        except ManifestError:
            previous = None
        manifest = build_manifest(project_root, config, previous)
        check_targets(config, manifest)

        carried = sum(1 for node in manifest.nodes if node.status == "clean")
        service = make_axle_service(config.axle)

        async def extract() -> Manifest:
            async with service:
                return await apply_extraction(service, manifest, project_root)

        manifest = asyncio.run(extract())
        payload_paths = write_compiled_payloads(manifest, project_root)
        written = save_manifest(manifest, project_root)
    except (ConfigError, ScanError, ManifestError, AxleServiceError, ExtractionError) as exc:
        raise click.ClickException(str(exc)) from exc

    counts = Counter(node.status for node in manifest.nodes)
    click.echo(
        f"Compiled {len(manifest.nodes)} file(s) across {len(config.modules)} "
        f"module(s): {counts.get('new', 0)} new, {counts.get('changed', 0)} changed, "
        f"{counts.get('clean', 0)} clean"
    )
    click.echo(
        f"Extraction: {len(manifest.nodes) - carried} extracted now, "
        f"{carried} carried over"
    )
    represented = {node.module for node in manifest.nodes}
    for module_name in config.modules:
        if module_name not in represented:
            click.echo(f"  Note: module '{module_name}' has no .lean files")
    click.echo(f"Wrote {len(payload_paths)} payload(s) to {compiled_payload_dir(project_root)}")
    click.echo(f"Wrote {written}")


@main.command("list")
@click.option(
    "--select",
    "select",
    default=None,
    help="Filter by <module>[.<file stem>[.<declaration>]].",
)
def list_declarations(select: str | None) -> None:
    """Print the parsed declaration tree in topological order (dependencies first)."""
    project_root = Path.cwd()
    try:
        config = load_config(project_root)
        manifest = load_manifest(project_root)
        if manifest.version != MANIFEST_VERSION:
            raise ManifestError(
                f"The manifest in {CACHE_DIRNAME}/ was written by an incompatible "
                f"axbt version; run `axbt compile` first."
            )
        selection = None
        if select is not None:
            selection = resolve_selection(select, config, manifest)
            nodes = selection.payload_nodes(manifest)
        else:
            nodes = manifest.nodes
        ordered = topological_order(nodes)
    except (ConfigError, ManifestError, SelectionError) as exc:
        raise click.ClickException(str(exc)) from exc

    for node in ordered:
        click.echo(f"{node.name} ({node.path})")
        if not node.declarations:
            click.echo("    (no declarations extracted)")
        for declaration in node.declarations:
            if selection is not None and selection.declaration is not None:
                if declaration.name != selection.declaration:
                    continue
            sorry = ", sorry" if declaration.is_sorry else ""
            click.echo(f"    {declaration.kind} {declaration.name} [line {declaration.line_pos}{sorry}]")
