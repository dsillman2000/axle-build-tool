"""The `axbt` command-line interface.

Command-line mechanics are implemented with `click`. The CLI ships
`axbt init`, `axbt compile`, `axbt check`, `axbt verify`, and
`axbt list`.
"""

from __future__ import annotations

import asyncio
import logging
import os
import re
import time
from collections import Counter
from dataclasses import dataclass, field
from datetime import datetime, timezone
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
    verification_signature,
)
from axle_build_tool.payloads import (
    Payload,
    build_payload,
    compiled_payload_dir,
    source_position,
    write_compiled_payloads,
)
from axle_build_tool.scanner import ScanError, scan_module
from axle_build_tool.stubbing import STUBBABLE_KINDS, bare_name
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
    # Diagnostics mode: AXBT_DEBUG=1 turns on per-node request logging
    # (dispatch/completion timings) for compile/check/verify runs.
    if os.environ.get("AXBT_DEBUG"):
        logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")


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
    """Compile the project in place; shared by `compile` and the
    precursor of every submission command.

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
    except (
        ConfigError,
        ScanError,
        ManifestError,
        AxleServiceError,
        ExtractionError,
        OSError,
    ) as exc:
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


def _acquire_project_state(
    project_root: Path, *, no_compile: bool, incremental: bool
) -> tuple[ProjectConfig, Manifest]:
    """Load (or freshly compile) the config and manifest of `project_root`.

    Shared by the submission commands (`check`, `verify`): by default a
    compile runs first so the manifest is never stale; `--no-compile`
    takes the existing manifest at face value, and `--full-refresh`
    makes the precursor re-extract everything. The latter two conflict.
    """
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
        return config, manifest
    return _run_compile(project_root, full_refresh=not incremental)


def _build_plan(
    select: str | None, config: ProjectConfig, manifest: Manifest
) -> list[tuple[str, Selection, bool]]:
    """Resolve the submission plan shared by `check` and `verify`.

    With `--select`, a single selection labelled by the selector (and
    flagged explicit — the user named what to judge). Otherwise every
    configured `targets` entry of every module, labelled
    `<module>.<target>`, in declaration order with duplicates removed
    (not explicit: config-driven, so `--sorry` grants can skip them).
    """
    if select is not None:
        return [(select, resolve_selection(select, config, manifest), True)]
    plan: list[tuple[str, Selection, bool]] = []
    for module in config.modules.values():
        seen: set[tuple[str, str | None]] = set()
        for target in module.targets:
            selection = resolve_selection(f"{module.name}.{target}", config, manifest)
            key = (selection.node_name or "", selection.declaration)
            if key not in seen:
                seen.add(key)
                plan.append((f"{module.name}.{target}", selection, False))
    return plan


def _build_stub_map(
    selectors: tuple[str, ...] | list[str],
    config: ProjectConfig,
    manifest: Manifest,
) -> dict[str, frozenset[str] | None]:
    """Resolve `--sorry` selectors into per-node stub instructions.

    Maps node names to the declarations to stub in that node — `None`
    meaning every stubbable declaration. Repeatable selectors merge
    (an all-declarations stub absorbs narrower ones).
    """
    stub_map: dict[str, frozenset[str] | None] = {}
    for selector in selectors:
        selection = resolve_selection(selector, config, manifest)
        for node in selection.payload_nodes(manifest):
            names = (
                None
                if selection.declaration is None
                else frozenset({selection.declaration})
            )
            if node.name not in stub_map:
                stub_map[node.name] = names
            elif stub_map[node.name] is None or names is None:
                stub_map[node.name] = None
            else:
                stub_map[node.name] = stub_map[node.name] | names
    return stub_map


def _refine_stub_map(
    stub_map: dict[str, frozenset[str] | None],
    selection: Selection,
    label: str,
    manifest: Manifest,
    explicit: bool,
) -> dict[str, frozenset[str] | None]:
    """Apply `--sorry` grants to one selection, refining as needed.

    `--sorry X` *grants* X's declarations this run: their bodies become
    stubs in the payload and they are not judged. One exception: an
    explicit `--select` of a declaration carves that declaration out of
    the grant — the user asked to judge it, so its siblings in the
    granted node are stubbed instead ("stub my siblings, judge me").
    Naming only the selected declaration leaves nothing to judge or
    stub and is rejected as contradictory.
    """
    if not stub_map:
        return stub_map
    own = {node.name for node in selection.payload_nodes(manifest)}
    refined: dict[str, frozenset[str] | None] = {}
    for name, names in stub_map.items():
        if name not in own:
            refined[name] = names
            continue
        carve_out = (
            explicit
            and selection.declaration is not None
            and selection.node_name == name
        )
        if not carve_out:
            # The grant stands: this selection is (fully or partially)
            # taken as granted.
            refined[name] = names
            continue
        node = manifest.by_name()[name]
        if names is None:
            remaining = frozenset(
                d.name for d in node.declarations if d.kind in STUBBABLE_KINDS
            ) - {selection.declaration}
        else:
            remaining = names - {selection.declaration}
        if not remaining:
            raise SelectionError(
                f"--sorry {name!r}: the selection {label!r} is never stubbed."
            )
        refined[name] = remaining
    return refined


def _granted_skip_reason(
    selection: Selection,
    refined: dict[str, frozenset[str] | None],
    manifest: Manifest,
    explicit: bool,
) -> str | None:
    """The skip reason when `--sorry` grants the whole selection.

    A selection fully covered by a grant has nothing to judge — its
    declarations are taken as granted (stubbed). Explicit
    declaration-level selections are exempt (see `_refine_stub_map`).
    """
    if not refined:
        return None
    by_name = manifest.by_name()
    if selection.declaration is not None:
        if explicit:
            return None  # judged: carved out of the grant
        if selection.node_name not in refined:
            return None  # no grant touches this node
        names = refined[selection.node_name]
        if names is None or selection.declaration in names:
            return "taken as granted (--sorry)"
        return None
    # File/module-level: skipped only when every own node is fully granted.
    own = selection.payload_nodes(manifest)
    if own and all(
        node.name in refined and refined[node.name] is None for node in own
    ):
        return "taken as granted (--sorry)"
    return None


def _resolve_permitted_sorries(
    selectors: tuple[str, ...] | list[str],
    config: ProjectConfig,
    manifest: Manifest,
) -> frozenset[str]:
    """Resolve `--permitted-sorries` selectors into declaration names.

    A declaration-level selector excuses that declaration; a file- or
    module-level selector excuses every verifiable declaration in it.
    The names are the full extracted names (the API reports and matches
    qualified names — observed live).
    """
    permitted: set[str] = set()
    for selector in selectors:
        selection = resolve_selection(selector, config, manifest)
        for node in selection.payload_nodes(manifest):
            if selection.declaration is not None:
                permitted |= {selection.declaration}
            else:
                permitted |= {
                    d.name for d in node.declarations if d.kind in _VERIFY_KINDS
                }
    return frozenset(permitted)


def _validate_stub_closure(
    stub_map: dict[str, frozenset[str] | None],
    label: str,
    payload: Payload,
) -> bool:
    """Whether any `--sorry` target applies to this selection's payload.

    A stubbed node outside the payload is simply irrelevant here (the
    selection doesn't depend on it — there is nothing to stub), so this
    is not an error; the run-level check (`_require_stub_application`)
    only fails when a stub applies nowhere at all.
    """
    closure = set(payload.sections)
    return any(name in closure for name in stub_map)


def _require_stub_application(
    stub_map: dict[str, frozenset[str] | None],
    applied: set[str],
    plan: list[tuple[str, Selection]],
) -> None:
    """Fail when a `--sorry` target applies to no planned selection.

    A stub that is relevant to some selections but not others is fine
    (a default run checks every target; not all of them need the
    stub). Applying nowhere at all means a misunderstanding — most
    likely a mistyped selector — and is rejected.
    """
    never_applied = sorted(set(stub_map) - applied)
    if not never_applied:
        return
    labels = ", ".join(label for label, _, _ in plan)
    raise SelectionError(
        f"--sorry {', '.join(repr(name) for name in never_applied)}: not a "
        f"dependency of any planned selection ({labels}); stubbing applies "
        "to the selections' dependency closures."
    )


#: Leading position of a Lean diagnostic message, e.g. `-:28:8-28:24: error: …`
#: (`-` is the API's filename placeholder for submitted content).
_MESSAGE_POSITION = re.compile(r"^-:(\d+):(\d+)(?:-(\d+):(\d+))?(?=:)")


#: Lean's sorry warning text (backticks in current Lean, quotes seen in
#: older versions).
_SORRY_WARNING = re.compile(r"declaration uses [`']sorry[`']")


def _stub_context_line(
    stub_map: dict[str, frozenset[str] | None],
    selection: Selection,
    manifest: Manifest,
) -> str | None:
    """A dim report line describing a payload's stubs — always shown
    when stubs are present, so stubbing is never invisible."""
    if not stub_map:
        return None
    by_name = manifest.by_name()
    own = {node.name for node in selection.payload_nodes(manifest)}
    upstream = siblings = 0
    for name, names in stub_map.items():
        node = by_name.get(name)
        if node is None:
            continue
        count = (
            len([d for d in node.declarations if d.kind in STUBBABLE_KINDS])
            if names is None
            else len(names)
        )
        if name in own:
            siblings += count
        else:
            upstream += count
    parts = []
    if upstream:
        parts.append(
            f"upstream stubbed: {upstream} declaration{'s' if upstream != 1 else ''}"
        )
    if siblings:
        parts.append(
            f"siblings stubbed: {siblings} declaration{'s' if siblings != 1 else ''}"
        )
    return "; ".join(parts) or None


def _split_stub_warnings(
    messages: list[str],
    payload: Payload,
    stub_map: dict[str, frozenset[str] | None] | None,
) -> tuple[list[str], int]:
    """Split Lean messages into (kept, collapsed-count).

    In a `--sorry` run, the stubbed declarations' own `declaration uses
    'sorry'` warnings are report noise — the stubs are ours by
    construction. Warnings raised inside a stubbed node's payload
    section are collapsed into a count; everything else (including
    sorries outside the stubbed subtrees) is kept.
    """
    if not stub_map:
        return messages, 0
    stubbed_sections = [
        payload.sections[name] for name in stub_map if name in payload.sections
    ]
    kept: list[str] = []
    collapsed = 0
    for message in messages:
        position = _MESSAGE_POSITION.match(message)
        in_stubbed_section = (
            position is not None
            and _SORRY_WARNING.search(message) is not None
            and any(
                start <= int(position.group(1)) <= end
                for start, end in stubbed_sections
            )
        )
        if in_stubbed_section:
            collapsed += 1
        else:
            kept.append(message)
    return kept, collapsed


def _decl_verdict(node: ManifestNode, decl: ExtractedDecl, response: Any, payload: Payload) -> str:
    """The per-declaration verdict for a multi-declaration selection.

    The submission is one API call for the whole selection, so the
    split is derived from the response: the declaration's own entry in
    `failed_declarations`, or a Lean error whose payload position maps
    (through the line map) into the declaration's file span.
    """
    if response.okay:
        return click.style("OK", fg="green")
    if decl.name in response.failed_declarations:
        return click.style("FAIL", fg="red")
    start, _end = payload.sections[node.name]
    line_map = payload.line_map[node.name]
    #: The payload lines whose source counterpart lies inside the
    #: declaration's file span (the message positions are payload lines).
    span = {
        start + offset
        for offset in range(len(line_map))
        if decl.line_pos <= line_map[offset] <= decl.end_line_pos
    }
    for error in response.lean_messages.errors:
        position = _MESSAGE_POSITION.match(error)
        if position is not None and int(position.group(1)) in span:
            return click.style("FAIL", fg="red")
    return click.style("OK", fg="green")


def _printed_lines(
    label: str, selection: Selection, manifest: Manifest
) -> list[tuple[str, ManifestNode | None, ExtractedDecl | None]]:
    """The report lines a selection expands to.

    Declaration-level selections print their selector as a single line
    (the whole selection is one declaration). File/module-level
    selections expand into one line per declaration — the same
    granularity the default targets path reports at. Labels are
    canonical (`module.file-stem.bare-name`), so namespaced
    declarations don't repeat their namespace.
    """
    if selection.declaration is not None:
        return [(label, None, None)]
    expanded = [
        (f"{node.name}.{bare_name(decl)}", node, decl)
        for node in selection.payload_nodes(manifest)
        for decl in node.declarations
    ]
    return expanded or [(label, None, None)]


def _progress_counter(done: int, total: int) -> str:
    """A streaming report's progress counter, padded to align, e.g. `[ 3/12]`."""
    return f"[{done:{max(len(str(total)), 1)}}/{total}]"


def _timing_text(seconds: float) -> str:
    """A measured duration formatted for the report, e.g. `1.234s`."""
    return f"{seconds:.3f}s"


@dataclass
class _StreamingReport:
    """Mutable tallies for a streaming report.

    `check` and `verify` print each result the moment its submission
    completes, so the tallies and the progress counter mutate while the
    report renders instead of being computed up front.
    """

    line_total: int
    printed: int = 0
    failed: int = 0
    skipped: int = 0
    cached: int = 0
    #: Selections that stopped being judged because --fail-fast cut
    #: the run short — never submitted or never reported.
    cancelled: int = 0

    def counter(self) -> str:
        """The next printed line's progress counter, `[ 3/12]`-style."""
        self.printed += 1
        return _progress_counter(self.printed, self.line_total)


async def _mint_share_link(
    service: Any,
    request_id: str | None,
    links: dict[str, str | AxleServiceError],
    *,
    enabled: bool = True,
) -> None:
    """Conditionally mint one `--share` link into `links`.

    Best-effort and deduplicated: maps the id to its share URL, or to
    the `AxleServiceError` when that mint failed; a request id shared
    across selections mints once. Sharing is a convenience: callers
    warn on errors and never fail the run over them. Nothing is minted
    when `enabled` is false (`--share` was not passed).

    The mint retries briefly because it streams in the moment the
    response arrives — ahead of batch minting, the share service may
    not have the run persisted yet and answers "request not found";
    that clears within moments.
    """
    if enabled and request_id and request_id not in links:
        error: AxleServiceError | None = None
        for wait in (0.0, 0.25, 0.5):
            if wait:
                await asyncio.sleep(wait)
            try:
                links[request_id] = await service.share_link(request_id)
                error = None
                break
            except AxleServiceError as exc:
                error = exc
        if error is not None:
            links[request_id] = error


def _print_share_line(
    links: dict[str, str | AxleServiceError],
    request_id: str | None,
    *,
    earlier_run: bool = False,
) -> None:
    """The indented share line for one selection's request id, if any."""
    if not request_id or request_id not in links:
        return
    entry = links[request_id]
    if isinstance(entry, AxleServiceError):
        click.secho(f"    share: unavailable ({entry})", dim=True)
        return
    suffix = click.style(" (from the earlier run)", dim=True) if earlier_run else ""
    click.echo(f"    {click.style('share:', dim=True)} {entry}{suffix}")


def _print_share_summary(links: dict[str, str | AxleServiceError]) -> None:
    """The run-summary mention of how many links were minted."""
    minted = sum(1 for entry in links.values() if not isinstance(entry, AxleServiceError))
    if minted:
        click.secho(f"Share link(s) minted: {minted}", dim=True)


def _latest_verified_request_id(manifest: Manifest, names: list[str]) -> str | None:
    """The most recent verification's request id among `names`.

    Cached selections mint their share link from the request id
    recorded when the verification originally succeeded, so `--share`
    works without re-submitting; old manifests have no recorded ids.
    """
    best: tuple[datetime, str] | None = None
    for node in manifest.nodes:
        for decl in node.declarations:
            if (
                decl.name in names
                and decl.verified_request_id is not None
                and decl.verified_at is not None
            ):
                if best is None or decl.verified_at > best[0]:
                    best = (decl.verified_at, decl.verified_request_id)
    return best[1] if best else None


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
    "--sorry",
    "sorry",
    multiple=True,
    help=(
        "Stub the given dependency subtree's proof/definition bodies "
        "(signatures preserved; repeatable). The selection itself is "
        "never stubbed."
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
@click.option(
    "--share",
    "share",
    is_flag=True,
    default=False,
    help=(
        "Print a share link for every submission — the API's web view "
        "of that exact check run."
    ),
)
@click.option(
    "--fail-fast",
    "-x",
    "fail_fast",
    is_flag=True,
    default=False,
    help=(
        "Stop at the first failing selection: cancel all ongoing "
        "submissions and report the failure instead of finishing the "
        "rest of the run."
    ),
)
def check(
    no_compile: bool,
    incremental: bool,
    sorry: tuple[str, ...],
    select: str | None,
    share: bool,
    fail_fast: bool,
) -> None:
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

    With --fail-fast (-x), the first failed selection cancels every
    submission still in flight and stops the run early — remaining
    selections are reported as cancelled in the summary.
    """
    project_root = Path.cwd()
    try:
        config, manifest = _acquire_project_state(
            project_root, no_compile=no_compile, incremental=incremental
        )
        plan = _build_plan(select, config, manifest)
        stub_map = _build_stub_map(sorry, config, manifest) if sorry else {}
        stub_warnings: list[str] = []
        applied: set[str] = set()
        checks: list[tuple[str, Selection, Payload | None, dict, str | None]] = []
        for label, selection, explicit in plan:
            refined = _refine_stub_map(
                stub_map, selection, label, manifest, explicit
            )
            granted = _granted_skip_reason(selection, refined, manifest, explicit)
            if granted is not None:
                # Taken as granted: nothing in this selection is judged.
                checks.append((label, selection, None, refined, granted))
                applied |= set(refined)
                continue
            payload = build_payload(
                selection.payload_nodes(manifest),
                manifest,
                project_root,
                stubbed=refined or None,
                warnings=stub_warnings,
            )
            if _validate_stub_closure(refined, label, payload):
                applied |= set(refined)
            checks.append((label, selection, payload, refined, None))
        _require_stub_application(stub_map, applied, plan)
        for warning in dict.fromkeys(stub_warnings):
            click.secho(f"  warning: {warning}", fg="yellow")
    except (ConfigError, ManifestError, SelectionError, OSError) as exc:
        raise click.ClickException(str(exc)) from exc

    if not checks:
        click.echo("No targets configured in axbt_project.yml; nothing to check.")
        return

    paths = {node.name: node.path for node in manifest.nodes}
    service = make_axle_service(config.axle)

    #: Pad labels so the status column aligns across the report. The
    #: labels include every expanded declaration line.
    width = max(
        len(printed)
        for label, selection, _, _, granted in checks
        for printed, _, _ in (
            _printed_lines(label, selection, manifest)
            if granted is None
            else [(label, None, None)]
        )
    )
    #: The report streams in as results arrive; every printed line
    #: counts toward the progress counter.
    line_total = sum(
        len(_printed_lines(label, selection, manifest))
        if granted is None
        else 1
        for label, selection, _, _, granted in checks
    )
    report = _StreamingReport(line_total=line_total)
    share_links: dict[str, str | AxleServiceError] = {}

    async def submit_all() -> None:
        async with service:
            await service.validate_environment()
            semaphore = asyncio.Semaphore(service.max_concurrency)

            async def submit(
                item: tuple[str, Selection, Payload, dict, None],
            ) -> tuple[tuple[str, Selection, Payload, dict, None], Any, float]:
                label, selection, payload, _refined, _granted = item
                async with semaphore:
                    # Declaration-level selections focus the check by name;
                    # Axle resolves theorems/lemmas only — defs are rejected
                    # with "Theorem '<name>' not found".
                    mark = time.monotonic()
                    response = await service.check(
                        payload.content,
                        context=label,
                        names=[selection.declaration] if selection.declaration else None,
                    )
                return item, response, time.monotonic() - mark

            #: Granted selections report SKIP without a submission.
            for label, _selection, _payload, _refined, granted in checks:
                if granted is None:
                    continue
                report.skipped += 1
                click.echo(
                    f"{report.counter()} {label:<{width}}  "
                    f"{click.style('SKIP', dim=True)}"
                )
                click.secho(f"    {granted}", dim=True)

            submittable = [item for item in checks if item[2] is not None]
            #: Results print the moment each submission completes, in
            #: completion order, each line with its elapsed time. Tasks
            #: are created explicitly so --fail-fast can cancel the
            #: ones still in flight.
            pending: set[asyncio.Task[Any]] = {
                asyncio.create_task(submit(item)) for item in submittable
            }
            while pending:
                done, pending = await asyncio.wait(
                    pending, return_when=asyncio.FIRST_COMPLETED
                )
                processed_in_batch = 0
                for task in done:
                    processed_in_batch += 1
                    item, response, elapsed = task.result()
                    label, selection, payload, refined, _granted = item
                    if not response.okay:
                        report.failed += 1
                    for printed, node, decl in _printed_lines(label, selection, manifest):
                        if node is None:
                            status = (
                                click.style("OK", fg="green")
                                if response.okay
                                else click.style("FAIL", fg="red")
                            )
                        else:
                            status = _decl_verdict(node, decl, response, payload)
                        click.echo(
                            f"{report.counter()} {printed:<{width}}  {status}"
                            f"  {_timing_text(elapsed)}"
                        )
                    kept, _ = _split_stub_warnings(
                        [
                            *response.lean_messages.errors,
                            *response.lean_messages.warnings,
                        ],
                        payload,
                        stub_map,
                    )
                    for message in kept:
                        click.echo(f"    {_rewrite_message_position(message, payload, paths)}")
                    stub_line = _stub_context_line(refined, selection, manifest)
                    if stub_line:
                        click.secho(f"    {stub_line}", dim=True)
                    if (
                        not response.okay
                        and not response.lean_messages.errors
                        and response.failed_declarations
                    ):
                        click.echo(
                            f"    failed declarations: {', '.join(response.failed_declarations)}"
                        )
                    rid = (response.info or {}).get("request_id")
                    await _mint_share_link(service, rid, share_links, enabled=share)
                    _print_share_line(share_links, rid)
                    #: --fail-fast: the first failed selection cancels
                    #: every submission still in flight and stops the
                    #: run; adds already-done but as yet unreported
                    #: tasks to the cancelled count.
                    if fail_fast and not response.okay:
                        report.cancelled = len(pending) + len(done) - processed_in_batch
                        click.secho(
                            f"    fail-fast: cancelled {report.cancelled} "
                            "remaining selection(s)",
                            dim=True,
                        )
                        for left in pending:
                            left.cancel()
                        if pending:
                            await asyncio.gather(*pending, return_exceptions=True)
                        return

    started = time.monotonic()
    try:
        asyncio.run(submit_all())
    except AxleServiceError as exc:
        raise click.ClickException(str(exc)) from exc

    if stub_map:
        try:
            for _, selection, payload, _, _ in checks:
                if payload is None:
                    continue
                out = compiled_payload_dir(project_root)
                out.mkdir(parents=True, exist_ok=True)
                (out / selection.compiled_filename_variant("stubbed")).write_text(
                    payload.content, encoding="utf-8"
                )
        except OSError as exc:
            raise click.ClickException(str(exc)) from exc

    total = len(checks)
    total_timing = _timing_text(time.monotonic() - started)
    skipped_note = f", {report.skipped} skipped" if report.skipped else ""
    cancelled_note = (
        f", {report.cancelled} cancelled by fail-fast" if report.cancelled else ""
    )
    if report.failed:
        click.secho(
            f"Checked {total} selection(s): {report.failed} failed, "
            f"{total - report.failed - report.cancelled} OK"
            f"{skipped_note}{cancelled_note} in {total_timing}",
            fg="red",
        )
        _print_share_summary(share_links)
        raise click.exceptions.Exit(1)
    click.secho(
        f"Checked {total} selection(s): all OK{skipped_note} in {total_timing}",
        fg="green",
    )
    _print_share_summary(share_links)


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


#: Declaration kinds with a proof body — the things `axbt verify` checks.
_VERIFY_KINDS = frozenset({"theorem", "lemma", "example"})


def _mask_key(key: str) -> str:
    """A recognizable rendering of the API key for diagnostics."""
    return f"{key[:12]}..."


@main.command()
def debug() -> None:
    """Verify the Axle API key and print the project's configuration.

    A developer diagnostic: shows what axbt will use for this project —
    the `axbt_project.yml` settings, the state of the `.axbt/` cache,
    and whether the `AXLE_API_KEY` environment variable is set and
    accepted by the API. Exits 1 when the key is missing or rejected.
    """
    project_root = Path.cwd()

    # --- Project configuration -------------------------------------------
    click.secho("Project (axbt_project.yml):", bold=True)
    config: AxleConfig | None = None
    try:
        project = load_config(project_root)
        config = project.axle
    except ConfigError as exc:
        click.secho(f"  {exc}", dim=True)
        click.secho("  (the Axle API check below runs without project settings)", dim=True)

    if config is not None:
        name_note = f" (v{project.version})" if project.version else ""
        click.echo(f"  name:       {project.name}{name_note}")
        click.echo(f"  location:   {project_root}")
        for module in project.modules.values():
            click.secho(f"  module {module.name}:", bold=True)
            click.echo(f"    dir:       {module.dir or module.name}")
            targets = ", ".join(module.targets) if module.targets else "(none configured)"
            click.echo(f"    targets:   {targets}")
            try:
                files = scan_module(project.module_path(project_root, module.name))
                click.echo(f"    files:     {len(files)} scanned")
            except ScanError as exc:
                click.secho(f"    files:     {exc}", dim=True)
        click.echo(f"  axle:")
        pinned = config.environment
        environment_note = "pinned in axbt_project.yml" if pinned else "auto-select (latest the API serves)"
        click.echo(f"    environment:    {pinned or '(unpinned)'} — {environment_note}")
        click.echo(f"    timeout:        {config.timeout_seconds} s")
        options = (
            ", ".join(f"{key}={value}" for key, value in config.global_options.items())
            or "(none)"
        )
        click.echo(f"    global options: {options}")

    # --- Cache state ------------------------------------------------------
    click.secho("Cache (.axbt/):", bold=True)
    try:
        manifest = load_manifest(project_root)
        if manifest.version != MANIFEST_VERSION:
            raise ManifestError("stale version")
        from collections import Counter

        statuses = Counter(node.status for node in manifest.nodes)
        generated = manifest.generated_at.strftime("%Y-%m-%d %H:%M")
        click.echo(f"  manifest:    version {manifest.version}, generated {generated}")
        click.echo(
            f"  files:       {len(manifest.nodes)} "
            f"({statuses.get('clean', 0)} clean, {statuses.get('changed', 0)} changed, "
            f"{statuses.get('new', 0)} new)"
        )
        declarations = sum(len(node.declarations) for node in manifest.nodes)
        click.echo(f"  declarations: {declarations} extracted")
        payloads = list(compiled_payload_dir(project_root).glob("*.lean"))
        click.echo(f"  payloads:    {len(payloads)} in {compiled_payload_dir(project_root)}")
    except ManifestError as exc:
        click.secho(f"  manifest:    not usable ({exc})", dim=True)

    # --- Axle API ---------------------------------------------------------
    click.secho("Axle API:", bold=True)
    key = os.environ.get("AXLE_API_KEY", "")
    if not key:
        click.secho("  key:         NOT SET", fg="red")
        click.secho(
            "  Set AXLE_API_KEY (the SDK reads it from the environment) and retry.",
            fg="red",
        )
        raise click.exceptions.Exit(1)

    click.echo(f"  key:         {_mask_key(key)} (set)")
    axle_config = config or AxleConfig()
    service = make_axle_service(axle_config)

    async def probe() -> tuple[str, int, list[str]]:
        async with service:
            started = time.monotonic()
            served = await service.environments(
                timeout_seconds=axle_config.timeout_seconds
            )
            latency_ms = int((time.monotonic() - started) * 1000)
            resolved = await service.resolve_environment()
        available = sorted(str(entry["name"]) for entry in served)
        return resolved, latency_ms, available

    try:
        resolved, latency_ms, available = asyncio.run(probe())
    except AxleServiceError as exc:
        click.secho(f"  reachable:   no — {exc}", fg="red")
        raise click.exceptions.Exit(1) from exc

    click.echo(f"  reachable:   yes ({latency_ms} ms)")
    click.echo("  key valid:   yes")
    click.echo(f"  environment: {resolved} resolved; {len(available)} served by the API")


@dataclass
class _VerifyScope:
    """What of a selection `axbt verify` will (or won't) verify."""

    #: Declarations to verify in this run — also the `theorem2sorry`
    #: names focusing the formal statement. Empty = nothing to submit
    #: (everything cached or excused).
    to_verify: list[str]
    #: Declarations with a still-valid cached verification — excused
    #: from the sweep and skipped by the submission.
    cached: list[str] = field(default_factory=list)
    #: Other verifiable declarations in the payload whose incompleteness
    #: (a `sorry`, or a proof relying on axioms) the API should excuse —
    #: used to keep declaration-level selections focused on their own
    #: declaration instead of the whole payload.
    permitted: list[str] | None = None
    #: Set when the selection has nothing to verify (e.g. defs only).
    skip_reason: str | None = None
    #: Verifiable declarations carrying a `sorry` — failed locally
    #: without an API call, since they cannot pass verification.
    sorried: list[str] = field(default_factory=list)


def _verify_scope(
    selection: Selection,
    payload: Payload,
    manifest: Manifest,
    stub_map: dict[str, frozenset[str] | None] | None = None,
    user_permitted: frozenset[str] = frozenset(),
    force: bool = False,
    sig_of=None,
) -> _VerifyScope:
    by_name = manifest.by_name()
    closure = [by_name[node_name] for node_name in payload.sections]
    verifiable = [
        d for node in closure for d in node.declarations if d.kind in _VERIFY_KINDS
    ]
    # Declarations stubbed by `--sorry` are sorried by construction:
    # they are excused in the verification and skipped by the local
    # guard (their recorded is_sorry refers to the original source).
    stubbed_names: set[str] = set()
    for node_name, names in (stub_map or {}).items():
        node = by_name.get(node_name)
        if node is None:
            continue
        if names is None:
            stubbed_names |= {
                d.name for d in node.declarations if d.kind in STUBBABLE_KINDS
            }
        else:
            stubbed_names |= names
    excused = stubbed_names | set(user_permitted)

    def cache_valid(declaration: ExtractedDecl, node_name: str) -> bool:
        if force:
            return False
        return (
            declaration.verified_sig is not None
            and declaration.verified_sig == sig_of(node_name)
        )

    if selection.declaration is not None:
        node = by_name[selection.node_name]
        declaration = next(
            d for d in node.declarations if d.name == selection.declaration
        )
        if declaration.kind not in _VERIFY_KINDS:
            return _VerifyScope(
                to_verify=[],
                skip_reason=(
                    f"'{declaration.name}' is a {declaration.kind}; verify checks "
                    "theorems/lemmas only — use axbt check for definitions"
                ),
            )
        if declaration.name in user_permitted:
            return _VerifyScope(
                to_verify=[],
                skip_reason=(
                    f"'{declaration.name}' is excused (--permitted-sorries); "
                    "nothing to verify"
                ),
            )
        if declaration.is_sorry:
            return _VerifyScope(to_verify=[], sorried=[declaration.name])
        if cache_valid(declaration, selection.node_name):
            return _VerifyScope(
                to_verify=[], cached=[declaration.name], permitted=sorted(excused) or None
            )
        # The API sweeps the whole submitted content for incomplete
        # proofs; excuse the payload's other theorems and every stubbed,
        # cached, or user-permitted declaration so the selection is
        # judged only on its own proof.
        permitted = (
            {d.name for d in verifiable if d.name != declaration.name}
            | stubbed_names
            | set(user_permitted)
        )
        return _VerifyScope(
            to_verify=[declaration.name],
            permitted=sorted(permitted) or None,
        )

    # File/module-level: the formal statement covers every verifiable
    # declaration in the payload (the full dependency closure).
    if not verifiable:
        return _VerifyScope(
            to_verify=[], skip_reason="no theorems to verify (definitions only)"
        )
    cached = [
        d.name
        for node in closure
        for d in node.declarations
        if d.kind in _VERIFY_KINDS and cache_valid(d, node.name)
    ]
    permitted = stubbed_names | set(user_permitted) | set(cached)
    to_verify = [d.name for d in verifiable if d.name not in permitted]
    sorried = [
        d.name
        for d in verifiable
        if d.is_sorry and d.name not in excused and d.name in to_verify
    ]
    if sorried:
        return _VerifyScope(to_verify=[], sorried=sorried)
    return _VerifyScope(
        to_verify=to_verify,
        cached=cached,
        permitted=sorted(permitted) or None,
    )


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
        "files, so verifications run on freshly extracted data. The "
        "verification step itself always re-submits its selection."
    ),
)
@click.option(
    "--sorry",
    "sorry",
    multiple=True,
    help=(
        "Stub the given dependency subtree's proof/definition bodies "
        "(signatures preserved; repeatable); the stubbed declarations "
        "are automatically permitted in the verification. The selection "
        "itself is never stubbed."
    ),
)
@click.option(
    "--permitted-sorries",
    "permitted_sorries",
    multiple=True,
    help=(
        "Excuse the named incomplete declarations (selector grammar; "
        "repeatable) instead of failing on them. Excused declarations "
        "are never recorded as verified."
    ),
)
@click.option(
    "--force",
    is_flag=True,
    default=False,
    help="Re-verify even when a cached verification is still valid.",
)
@click.option(
    "--select",
    "select",
    default=None,
    help=(
        "Verify <module>[.<file stem>[.<declaration>]] instead of the "
        "configured targets. Declaration-level selections must name a "
        "theorem/lemma — definitions have no proof to verify."
    ),
)
@click.option(
    "--share",
    "share",
    is_flag=True,
    default=False,
    help=(
        "Print a share link for every verification submission, and for "
        "each selection's most recent cached verification."
    ),
)
@click.option(
    "--fail-fast",
    "-x",
    "fail_fast",
    is_flag=True,
    default=False,
    help=(
        "Stop at the first failing selection: cancel all ongoing "
        "submissions and report the failure instead of finishing the "
        "rest of the run."
    ),
)
def verify(
    no_compile: bool,
    incremental: bool,
    sorry: tuple[str, ...],
    permitted_sorries: tuple[str, ...],
    force: bool,
    select: str | None,
    share: bool,
    fail_fast: bool,
) -> None:
    """Verify proofs at kernel level via the Axle API.

    The rigorous counterpart to `axbt check`: for every selection, the
    payload's theorem proofs are stripped into a formal statement (the
    API's theorem2sorry transform — imports and local definitions are
    preserved, so statements referencing them stay verifiable), and the
    real content is checked against it kernel-level. Selection and run
    modes match `axbt check`, and selections carrying a `sorry` fail
    without an API call.

    Successful verifications are recorded per declaration in the
    manifest, keyed on the declaration's file-closure content, the
    environment, and the global options; a later verify skips
    selections whose declarations are all still validly cached, unless
    --force re-runs them.

    With --fail-fast (-x), the first failed selection cancels every
    submission still in flight and stops the run early — remaining
    selections are reported as cancelled in the summary.
    """
    project_root = Path.cwd()
    try:
        config, manifest = _acquire_project_state(
            project_root, no_compile=no_compile, incremental=incremental
        )
        plan = _build_plan(select, config, manifest)
        stub_map = _build_stub_map(sorry, config, manifest) if sorry else {}
        user_permitted = _resolve_permitted_sorries(
            permitted_sorries, config, manifest
        )
        stub_warnings: list[str] = []
        applied: set[str] = set()
    except (ConfigError, ManifestError, SelectionError, OSError) as exc:
        raise click.ClickException(str(exc)) from exc

    if not plan:
        click.echo("No targets configured in axbt_project.yml; nothing to verify.")
        return

    paths = {node.name: node.path for node in manifest.nodes}
    by_name = manifest.by_name()
    node_of_decl = {
        d.name: node.name for node in manifest.nodes for d in node.declarations
    }
    service = make_axle_service(config.axle)

    async def prepare() -> str:
        async with service:
            await service.validate_environment()
            return await service.resolve_environment()

    try:
        environment = asyncio.run(prepare())
    except AxleServiceError as exc:
        raise click.ClickException(str(exc)) from exc

    sig_cache: dict[str, str] = {}

    def sig_of(node_name: str) -> str:
        if node_name not in sig_cache:
            sig_cache[node_name] = verification_signature(
                by_name[node_name],
                manifest,
                environment,
                config.axle.global_options,
            )
        return sig_cache[node_name]

    try:
        items: list[tuple[str, Selection, Payload | None, dict, str | None, _VerifyScope | None]] = []
        for label, selection, explicit in plan:
            refined = _refine_stub_map(
                stub_map, selection, label, manifest, explicit
            )
            granted = _granted_skip_reason(selection, refined, manifest, explicit)
            if granted is not None:
                # Taken as granted: nothing in this selection is judged.
                items.append((label, selection, None, refined, granted, None))
                applied |= set(refined)
                continue
            payload = build_payload(
                selection.payload_nodes(manifest),
                manifest,
                project_root,
                stubbed=refined or None,
                warnings=stub_warnings,
            )
            if _validate_stub_closure(refined, label, payload):
                applied |= set(refined)
            # User-permitted declarations must belong to this payload.
            closure_decls = {
                d.name
                for node_name in payload.sections
                for d in by_name[node_name].declarations
            }
            missing = user_permitted - closure_decls
            if missing:
                raise SelectionError(
                    "--permitted-sorries: "
                    f"{', '.join(sorted(missing))} not part of {label!r}'s payload."
                )
            items.append(
                (
                    label,
                    selection,
                    payload,
                    refined,
                    None,
                    _verify_scope(
                        selection,
                        payload,
                        manifest,
                        refined,
                        user_permitted=user_permitted,
                        force=force,
                        sig_of=sig_of,
                    ),
                )
            )
        _require_stub_application(stub_map, applied, plan)
        for warning in dict.fromkeys(stub_warnings):
            click.secho(f"  warning: {warning}", fg="yellow")
    except (ConfigError, ManifestError, SelectionError, OSError) as exc:
        raise click.ClickException(str(exc)) from exc

    submittable = [
        item
        for item in items
        if item[5] is not None
        and item[5].skip_reason is None
        and not item[5].sorried
        and item[5].to_verify
    ]

    report = _StreamingReport(line_total=len(items))
    #: Pad labels so the status column aligns across the report.
    width = max(len(label) for label, _, _, _, _, _ in items)
    share_links: dict[str, str | AxleServiceError] = {}
    stamps: dict[str, tuple[str, datetime, str | None]] = {}

    async def submit_all() -> None:
        async with service:
            #: Cached selections mint their share link from the request
            #: id recorded when the verification originally succeeded —
            #: known before anything streams in.
            for label, _selection, _payload, _refined, granted, scope in items:
                if granted is not None or scope is None or scope.to_verify:
                    continue
                if scope.cached:
                    await _mint_share_link(
                        service,
                        _latest_verified_request_id(manifest, scope.cached),
                        share_links,
                        enabled=share,
                    )
            #: Selections judged without a submission report first; the
            #: streamed verdicts print the moment each submission
            #: completes, in completion order, with its elapsed time.
            stopped = False
            for label, _selection, payload, _refined, granted, scope in items:
                if granted is not None:
                    report.skipped += 1
                    click.echo(
                        f"{report.counter()} {label:<{width}}  "
                        f"{click.style('SKIP', dim=True)}"
                    )
                    click.secho(f"    {granted}", dim=True)
                    continue
                assert scope is not None and payload is not None
                if scope.skip_reason is not None:
                    report.skipped += 1
                    click.echo(
                        f"{report.counter()} {label:<{width}}  "
                        f"{click.style('SKIP', dim=True)}"
                    )
                    click.secho(f"    {scope.skip_reason}", dim=True)
                    continue
                if scope.sorried:
                    report.failed += 1
                    click.echo(
                        f"{report.counter()} {label:<{width}}  "
                        f"{click.style('FAIL', fg='red')}"
                    )
                    for name in scope.sorried:
                        click.echo(
                            f"    declaration '{name}' has a `sorry`; "
                            "verify requires complete proofs"
                        )
                    #: --fail-fast: a local failure stops the run before
                    #: any submission is made.
                    if fail_fast:
                        report.cancelled = report.line_total - report.printed
                        click.secho(
                            f"    fail-fast: cancelled {report.cancelled} "
                            "remaining selection(s)",
                            dim=True,
                        )
                        stopped = True
                        break
                    continue
                if not scope.to_verify:
                    report.cached += 1
                    note = "cached" if scope.cached else "nothing to submit"
                    click.echo(
                        f"{report.counter()} {label:<{width}}  "
                        f"{click.style('OK', fg='green')} ({note})"
                    )
                    if scope.cached:
                        rid = _latest_verified_request_id(manifest, scope.cached)
                        _print_share_line(share_links, rid, earlier_run=True)
                    continue

            if not stopped:
                semaphore = asyncio.Semaphore(service.max_concurrency)

                async def submit(
                    item: tuple[str, Selection, Payload, dict, str | None, _VerifyScope],
                ) -> tuple[
                    tuple[str, Selection, Payload, dict, str | None, _VerifyScope],
                    Any,
                    float,
                ]:
                    label, _selection, payload, _refined, _granted, scope = item
                    async with semaphore:
                        # The formal statement is the payload with exactly
                        # the to-verify theorems' proofs stripped; cached,
                        # permitted, and stubbed declarations stay as they
                        # are (and are excused from the sweep).
                        mark = time.monotonic()
                        spec = await service.theorem2sorry(
                            payload.content,
                            context=label,
                            theorems_only=True,
                            names=scope.to_verify,
                        )
                        response = await service.verify_proof(
                            spec.content,
                            payload.content,
                            context=label,
                            permitted_sorries=scope.permitted,
                        )
                    return item, response, time.monotonic() - mark

                #: Results print the moment each submission completes,
                #: in completion order, each line with its elapsed time.
                #: Tasks are created explicitly so --fail-fast can cancel
                #: the ones still in flight.
                pending: set[asyncio.Task[Any]] = {
                    asyncio.create_task(submit(item)) for item in submittable
                }
                while pending:
                    done, pending = await asyncio.wait(
                        pending, return_when=asyncio.FIRST_COMPLETED
                    )
                    processed_in_batch = 0
                    for task in done:
                        processed_in_batch += 1
                        item, response, elapsed = task.result()
                        label, selection, payload, refined, _granted, scope = item
                        rid = (response.info or {}).get("request_id")
                        # A provable negation means the statement is
                        # vacuous — the outcome is reported only when
                        # the API ran the negation check.
                        vacuous = (
                            response.negation is not None and response.negation.okay
                        )
                        if response.okay and not vacuous:
                            now = datetime.now(timezone.utc)
                            for name in scope.to_verify:
                                stamps[name] = (sig_of(node_of_decl[name]), now, rid)
                            cached_note = (
                                f", {len(scope.cached)} cached" if scope.cached else ""
                            )
                            click.echo(
                                f"{report.counter()} {label:<{width}}  "
                                f"{click.style('OK', fg='green')}{cached_note}"
                                f"  {_timing_text(elapsed)}"
                            )
                        else:
                            report.failed += 1
                            click.echo(
                                f"{report.counter()} {label:<{width}}  "
                                f"{click.style('FAIL', fg='red')}  {_timing_text(elapsed)}"
                            )
                            if vacuous:
                                click.echo(
                                    "    the negation is also provable; "
                                    "the statement is vacuous"
                                )
                        kept, _ = _split_stub_warnings(
                            [
                                *response.lean_messages.errors,
                                *response.lean_messages.warnings,
                            ],
                            payload,
                            stub_map,
                        )
                        for message in kept:
                            click.echo(
                                f"    {_rewrite_message_position(message, payload, paths)}"
                            )
                        stub_line = _stub_context_line(refined, selection, manifest)
                        if stub_line:
                            click.secho(f"    {stub_line}", dim=True)
                        if (
                            not response.okay
                            and not response.lean_messages.errors
                            and response.failed_declarations
                        ):
                            click.echo(
                                f"    failed declarations: {', '.join(response.failed_declarations)}"
                            )
                        await _mint_share_link(
                            service, rid, share_links, enabled=share
                        )
                        _print_share_line(share_links, rid)
                        #: --fail-fast: the first failed selection cancels
                        #: every submission still in flight and stops the
                        #: run; already-done but unreported tasks count as
                        #: cancelled too.
                        if fail_fast and not (response.okay and not vacuous):
                            report.cancelled = (
                                len(pending) + len(done) - processed_in_batch
                            )
                            click.secho(
                                f"    fail-fast: cancelled {report.cancelled} "
                                "remaining selection(s)",
                                dim=True,
                            )
                            for left in pending:
                                left.cancel()
                            if pending:
                                await asyncio.gather(
                                    *pending, return_exceptions=True
                                )
                            return

    started = time.monotonic()
    try:
        asyncio.run(submit_all())
    except AxleServiceError as exc:
        raise click.ClickException(str(exc)) from exc

    if stub_map:
        try:
            for _, selection, payload, _, _, _ in items:
                if payload is None:
                    continue
                out = compiled_payload_dir(project_root)
                out.mkdir(parents=True, exist_ok=True)
                (out / selection.compiled_filename_variant("stubbed")).write_text(
                    payload.content, encoding="utf-8"
                )
        except OSError as exc:
            raise click.ClickException(str(exc)) from exc

    if stamps:
        stamped = set(stamps)
        nodes = []
        for node in manifest.nodes:
            node_stamps = {n for n in stamped if node_of_decl.get(n) == node.name}
            if not node_stamps:
                nodes.append(node)
                continue
            sig, now, rid = next(stamps[n] for n in node_stamps)
            declarations = [
                d.model_copy(
                    update={
                        "verified_sig": sig,
                        "verified_at": now,
                        "verified_request_id": rid,
                    }
                )
                if d.name in node_stamps
                else d
                for d in node.declarations
            ]
            nodes.append(node.model_copy(update={"declarations": declarations}))
        manifest = manifest.model_copy(update={"nodes": nodes})
        try:
            save_manifest(manifest, project_root)
        except OSError as exc:
            raise click.ClickException(str(exc)) from exc
        click.secho(f"Recorded {len(stamps)} verification(s) in the manifest", dim=True)

    total = len(items)
    total_timing = _timing_text(time.monotonic() - started)
    ok = total - report.failed - report.skipped - report.cancelled
    skipped_note = f", {report.skipped} skipped" if report.skipped else ""
    cancelled_note = (
        f", {report.cancelled} cancelled by fail-fast" if report.cancelled else ""
    )
    cached_note = f" ({report.cached} cached)" if report.cached else ""
    if report.failed:
        click.secho(
            f"Verified {total} selection(s): {report.failed} failed, {ok} OK"
            f"{skipped_note}{cancelled_note} in {total_timing}",
            fg="red",
        )
        _print_share_summary(share_links)
        raise click.exceptions.Exit(1)
    click.secho(
        f"Verified {total} selection(s): all OK{skipped_note}{cached_note}"
        f" in {total_timing}",
        fg="green",
    )
    _print_share_summary(share_links)


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
