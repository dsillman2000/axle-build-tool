"""The `axbt` command-line interface.

Command-line mechanics are implemented with `click`. The CLI ships
`axbt init`, `axbt compile`, `axbt check`, and `axbt list`;
kernel-level proof verification (`axbt verify`) will follow.
"""

from __future__ import annotations

import asyncio
import re
from collections import Counter
from pathlib import Path
from typing import Any

import click

from axle_build_tool.axle_service import AxleService, AxleServiceError
from axle_build_tool.config import (
    CACHE_DIRNAME,
    CONFIG_FILENAME,
    AxleConfig,
    ConfigError,
    ProjectConfig,
    load_config,
    scaffold_config,
)
from axle_build_tool.extraction import ExtractionError, apply_extraction
from axle_build_tool.manifest import (
    MANIFEST_VERSION,
    ExtractedDecl,
    ManifestError,
    ManifestNode,
    build_manifest,
    check_targets,
    load_manifest,
    save_manifest,
    topological_order,
)
from axle_build_tool.payloads import (
    Payload,
    build_payload,
    compiled_payload_dir,
    source_position,
    write_compiled_payloads,
)
from axle_build_tool.scanner import ScanError
from axle_build_tool.selection import Selection, SelectionError, resolve_selection

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


def _run_compile(
    project_root: Path, full_refresh: bool = False
) -> tuple[ProjectConfig, Manifest]:
    """Compile the project in place; shared by `compile` and `check`.

    Scans modules, updates the manifest, extracts pending declarations
    via Axle, persists payloads, and writes `.axbt/manifest.json`.
    Prints the usual compile summary. Returns the loaded config and the
    fresh manifest.

    Two run modes: **incremental** (the default) re-extracts only new
    and changed files, carrying clean nodes' extraction data over by
    MD5; **full refresh** ignores the previous manifest entirely and
    re-extracts every file. A fully incremental project whose files are
    all clean makes no API calls at all (including environment
    validation — there is nothing to submit it would guard).
    """
    try:
        config = load_config(project_root)
        previous = None
        if not full_refresh:
            try:
                # A missing, damaged, or stale-versioned manifest simply
                # means we start fresh (everything gets re-extracted).
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
                if carried < len(manifest.nodes):
                    await service.validate_environment()
                return await apply_extraction(service, manifest, project_root)

        manifest = asyncio.run(extract())
        payload_paths = write_compiled_payloads(manifest, project_root)
        written = save_manifest(manifest, project_root)
    except (ConfigError, ScanError, ManifestError, AxleServiceError, ExtractionError) as exc:
        raise click.ClickException(str(exc)) from exc

    counts = Counter(node.status for node in manifest.nodes)
    new_count, changed_count, clean_count = (
        counts.get("new", 0),
        counts.get("changed", 0),
        counts.get("clean", 0),
    )
    click.echo(
        f"Compiled {len(manifest.nodes)} file(s) across {len(config.modules)} "
        f"module(s): {click.style(f'{new_count} new', fg='green')}, "
        f"{click.style(f'{changed_count} changed', fg='yellow')}, "
        f"{click.style(f'{clean_count} clean', fg='cyan')}"
    )
    click.echo(
        f"Extraction: {click.style(f'{len(manifest.nodes) - carried} extracted now', fg='green')}, "
        f"{click.style(f'{carried} carried over', fg='cyan')}"
    )
    represented = {node.module for node in manifest.nodes}
    for module_name in config.modules:
        if module_name not in represented:
            click.secho(f"  Note: module '{module_name}' has no .lean files", dim=True)
    click.secho(
        f"Wrote {len(payload_paths)} payload(s) to {compiled_payload_dir(project_root)}",
        dim=True,
    )
    click.secho(f"Wrote {written}", dim=True)
    return config, manifest


@main.command()
@click.option(
    "--incremental/--full-refresh",
    "incremental",
    default=True,
    help=(
        "Run mode. Incremental (default) re-extracts only new and changed "
        "files, carrying clean files' extraction data over by content hash. "
        "--full-refresh ignores the previous manifest and re-extracts "
        "everything, even unchanged files."
    ),
)
def compile(incremental: bool) -> None:
    """Scan modules, extract declarations via Axle, and write .axbt/manifest.json."""
    _run_compile(Path.cwd(), full_refresh=not incremental)


#: Leading position of a Lean diagnostic message, e.g. `-:28:8-28:24: error: …`
#: (`-` is the API's filename placeholder for submitted content).
_MESSAGE_POSITION = re.compile(r"^-:(\d+):(\d+)(?:-(\d+):(\d+))?(?=:)")


def _rewrite_message_position(
    message: str, payload: Payload, paths: dict[str, str]
) -> str:
    """Attribute a Lean diagnostic's payload position to its source file.

    Check responses report positions in payload coordinates with a `-`
    filename placeholder; rewrite the leading position (both ends of a
    range) into `<file>:<line>` form using the payload's line map.
    Messages without a mappable leading position (e.g. errors on the
    hoisted import header) are returned unchanged.
    """
    match = _MESSAGE_POSITION.match(message)
    if match is None:
        return message

    def locate(line: str) -> str | None:
        found = source_position(payload, int(line))
        if found is None:
            return None
        node_name, source_line = found
        return f"{paths.get(node_name, node_name)}:{source_line}"

    start_line, start_col, end_line, end_col = match.groups()
    start = locate(start_line)
    if start is None or (end_line is not None and locate(end_line) is None):
        return message
    prefix = f"{start}:{start_col}"
    if end_line is not None:
        prefix += f"-{locate(end_line)}:{end_col}"
    return prefix + message[match.end():]


@main.command()
@click.option(
    "--no-compile",
    "no_compile",
    is_flag=True,
    default=False,
    help="Use the existing manifest at face value instead of recompiling first.",
)
@click.option(
    "--incremental/--full-refresh",
    "incremental",
    default=True,
    help=(
        "Run mode of the precursor compile. Incremental (default) "
        "re-extracts only new and changed files. --full-refresh ignores "
        "the previous manifest and re-extracts everything, even unchanged "
        "files, so checks run on freshly extracted data. The check step "
        "itself always re-submits its selection."
    ),
)
@click.option(
    "--select",
    "select",
    default=None,
    help=(
        "Check <module>[.<file stem>[.<declaration>]] instead of the configured "
        "targets. Declaration-level selections must name a theorem/lemma: Axle's "
        "focused checking resolves theorems by name only, not defs — select the "
        "file or module to check definitions."
    ),
)
def check(no_compile: bool, incremental: bool, select: str | None) -> None:
    """Typecheck targets or a selection via the Axle API.

    By default, check runs `axbt compile` first — scanning modules,
    detecting changes, and re-extracting whatever moved — so the
    manifest (and the selection metadata built from it) is never stale.
    The precursor is fully incremental: when every file is already
    clean it makes no API calls. Pass --full-refresh to make the
    precursor re-extract everything, or --no-compile to skip it and
    take the existing manifest at face value.

    Without --select, checks every configured `targets` entry of every
    module (one Axle `check` call per target). Submissions are standalone
    payloads — dependencies inlined — so even a single declaration is
    checked in full context. This is the fast, lightweight tier;
    kernel-level proof verification is `axbt verify`.

    Declaration-level selections pass `names=[<declaration>]` so Axle
    focuses the check; Axle resolves names against theorems/lemmas only
    (a `def` name is rejected with "Theorem '<name>' not found"), so
    definitions must be checked via file- or module-level selections.
    """
    project_root = Path.cwd()
    if no_compile and not incremental:
        raise click.UsageError(
            "--full-refresh conflicts with --no-compile: skipping "
            "compilation leaves nothing to refresh."
        )
    if no_compile:
        try:
            config = load_config(project_root)
            manifest = load_manifest(project_root)
            if manifest.version != MANIFEST_VERSION:
                raise ManifestError(
                    f"The manifest in {CACHE_DIRNAME}/ was written by an incompatible "
                    f"axbt version; run `axbt compile` first."
                )
        except (ConfigError, ManifestError) as exc:
            raise click.ClickException(str(exc)) from exc
    else:
        config, manifest = _run_compile(project_root, full_refresh=not incremental)

    try:
        if select is not None:
            plan: list[tuple[str, Selection]] = [
                (select, resolve_selection(select, config, manifest))
            ]
        else:
            plan = []
            for module in config.modules.values():
                seen: set[tuple[str, str | None]] = set()
                for target in module.targets:
                    selection = resolve_selection(
                        f"{module.name}.{target}", config, manifest
                    )
                    key = (selection.node_name or "", selection.declaration)
                    if key not in seen:
                        seen.add(key)
                        plan.append((f"{module.name}.{target}", selection))
        checks = [
            (
                label,
                selection,
                build_payload(
                    selection.payload_nodes(manifest), manifest, project_root
                ),
            )
            for label, selection in plan
        ]
    except SelectionError as exc:
        raise click.ClickException(str(exc)) from exc

    if not checks:
        click.echo("No targets configured in axbt_project.yml; nothing to check.")
        return

    paths = {node.name: node.path for node in manifest.nodes}
    service = make_axle_service(config.axle)

    async def submit_all() -> list[Any]:
        async with service:
            await service.validate_environment()
            semaphore = asyncio.Semaphore(service.max_concurrency)

            async def submit(item: tuple[str, Selection, Payload]) -> Any:
                label, selection, payload = item
                async with semaphore:
                    # Declaration-level selections focus the check by name;
                    # Axle resolves theorems/lemmas only — defs are rejected
                    # with "Theorem '<name>' not found".
                    return await service.check(
                        payload.content,
                        context=label,
                        names=[selection.declaration] if selection.declaration else None,
                    )

            return list(await asyncio.gather(*(submit(item) for item in checks)))

    try:
        responses = asyncio.run(submit_all())
    except AxleServiceError as exc:
        raise click.ClickException(str(exc)) from exc

    failed = 0
    #: Pad labels so the status column aligns across the report.
    width = max(len(label) for label, _, _ in checks)
    for (label, _, payload), response in zip(checks, responses):
        if response.okay:
            status = click.style("OK", fg="green")
        else:
            failed += 1
            status = click.style("FAIL", fg="red")
        click.echo(f"{label:<{width}}  {status}")
        messages = [
            *response.lean_messages.errors,
            *response.lean_messages.warnings,
        ]
        for message in messages:
            click.echo(f"    {_rewrite_message_position(message, payload, paths)}")
        if (
            not response.okay
            and not response.lean_messages.errors
            and response.failed_declarations
        ):
            click.echo(
                f"    failed declarations: {', '.join(response.failed_declarations)}"
            )
    total = len(checks)
    if failed:
        click.secho(
            f"Checked {total} selection(s): {failed} failed, {total - failed} OK",
            fg="red",
        )
        raise click.exceptions.Exit(1)
    click.secho(f"Checked {total} selection(s): all OK", fg="green")


#: Colors for declaration kinds in `axbt list` (unknown kinds stay plain).
_KIND_COLORS = {
    "theorem": "green",
    "lemma": "green",
    "example": "green",
    "def": "cyan",
    "abbrev": "cyan",
    "structure": "magenta",
    "class": "magenta",
    "inductive": "magenta",
    "instance": "magenta",
}


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

    # Gather the visible rows first so columns can align across the
    # whole listing (the --select declaration filter is applied here).
    sections: list[tuple[ManifestNode, list[ExtractedDecl]]] = []
    for node in ordered:
        declarations = [
            declaration
            for declaration in node.declarations
            if not (
                selection is not None
                and selection.declaration is not None
                and declaration.name != selection.declaration
            )
        ]
        sections.append((node, declarations))

    kind_width = max((len(d.kind) for _, ds in sections for d in ds), default=0)
    name_width = max((len(d.name) for _, ds in sections for d in ds), default=0)
    line_width = max(
        (len(str(d.line_pos)) for _, ds in sections for d in ds), default=1
    )

    for node, declarations in sections:
        click.secho(node.name, bold=True, nl=False)
        click.secho(f" ({node.path})", dim=True)
        if not declarations:
            click.secho("    (no declarations extracted)", dim=True)
            continue
        for declaration in declarations:
            kind = click.style(
                declaration.kind.ljust(kind_width),
                fg=_KIND_COLORS.get(declaration.kind),
            )
            name = declaration.name.ljust(name_width)
            position = click.style(
                f"[line {declaration.line_pos:>{line_width}}", dim=True
            )
            if declaration.is_sorry:
                position += ", " + click.style("sorry", fg="yellow")
            position += click.style("]", dim=True)
            click.echo(f"    {kind}  {name}  {position}")
