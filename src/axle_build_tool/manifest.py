"""Dependency DAG construction and `manifest.json` persistence.

`axbt compile` scans every configured module, parses imports, and writes
the project's dependency DAG to `.axbt/manifest.json`. Each node tracks
its source path, direct parents/children, an MD5 fingerprint of its
source (for incremental change detection), and a status.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, ValidationError

from axle_build_tool.config import CACHE_DIRNAME, ProjectConfig
from axle_build_tool.imports import parse_imports
from axle_build_tool.scanner import scan_module

MANIFEST_FILENAME = "manifest.json"
MANIFEST_VERSION = 2


class ManifestError(Exception):
    """Raised when a manifest is missing or invalid, or when the source
    files cannot be assembled into an acyclic dependency graph."""


class ExtractedDecl(BaseModel):
    """Per-declaration metadata extracted from a node by the Axle API."""

    model_config = ConfigDict(extra="forbid", frozen=True)

    name: str
    kind: str
    is_sorry: bool
    line_pos: int
    end_line_pos: int
    signature: str = ""


class ManifestNode(BaseModel):
    """One `.lean` file in the project DAG.

    `status` is the MD5-diff verdict on the source against the previous
    manifest (`new`, `clean`, `changed`). `declarations` holds the
    Axle-extracted metadata; compile is all-or-nothing, so a *persisted*
    manifest always carries valid extraction data for every node — a
    clean node's data is carried over, anything else is re-extracted.
    """

    model_config = ConfigDict(extra="forbid", frozen=True)

    name: str
    module: str
    path: str
    imports: list[str] = Field(default_factory=list)
    parents: list[str] = Field(default_factory=list)
    children: list[str] = Field(default_factory=list)
    md5: str
    status: Literal["new", "clean", "changed"]
    declarations: list[ExtractedDecl] = Field(default_factory=list)
    last_checked: datetime | None = None


class Manifest(BaseModel):
    """The persisted project DAG (`manifest.json`)."""

    model_config = ConfigDict(extra="forbid", frozen=True)

    version: int = MANIFEST_VERSION
    generated_at: datetime
    nodes: list[ManifestNode] = Field(default_factory=list)

    def by_name(self) -> dict[str, ManifestNode]:
        return {node.name: node for node in self.nodes}


@dataclass
class _Facts:
    """Raw per-file facts collected during the scan."""

    name: str
    module: str
    path: str
    dotted_stem: str
    md5: str
    imports: list[str]


def manifest_path(project_root: Path) -> Path:
    return project_root / CACHE_DIRNAME / MANIFEST_FILENAME


def load_manifest(project_root: Path) -> Manifest:
    """Load and validate `.axbt/manifest.json` from `project_root`."""
    path = manifest_path(project_root)
    if not path.is_file():
        raise ManifestError(
            f"No {MANIFEST_FILENAME} found in {CACHE_DIRNAME}/; run `axbt compile` first."
        )
    try:
        return Manifest.model_validate_json(path.read_text(encoding="utf-8"))
    except ValidationError as exc:
        raise ManifestError(f"Invalid {MANIFEST_FILENAME}: {exc}") from exc


def save_manifest(manifest: Manifest, project_root: Path) -> Path:
    """Write `manifest` to `.axbt/manifest.json`, creating `.axbt/` if needed."""
    path = manifest_path(project_root)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(manifest.model_dump_json(indent=2) + "\n", encoding="utf-8")
    return path


def _dotted_stem(relative_path: Path) -> str:
    """The dotted stem of a module-relative file: `Utils/Basic.lean` -> `Utils.Basic`."""
    return relative_path.with_suffix("").as_posix().replace("/", ".")


def _resolve_import(
    node: _Facts,
    imported: str,
    stem_index: dict[str, list[str]],
    scanned: dict[str, _Facts],
) -> str | None:
    """Resolve an import name to a node name, or None if it is external."""
    candidates = stem_index.get(imported, [])
    if not candidates:
        return None  # Not a project file: Lean core, std, Mathlib, ...
    same_module = [c for c in candidates if scanned[c].module == node.module]
    if same_module:
        return same_module[0]
    if len(candidates) == 1:
        return candidates[0]
    raise ManifestError(
        f"Import '{imported}' in {node.name} is ambiguous; it matches: "
        f"{', '.join(sorted(candidates))}. Rename the files so file stems are unique."
    )


def _detect_cycle(parents: dict[str, list[str]]) -> None:
    """Raise `ManifestError` if the `parents` graph contains a cycle."""
    state: dict[str, int] = dict.fromkeys(parents, 0)  # 0=new, 1=in progress, 2=done
    for start in sorted(parents):
        if state[start]:
            continue
        path = [start]
        state[start] = 1
        stack = [iter(parents[start])]
        while stack:
            candidate = next(stack[-1], None)
            if candidate is None:
                state[path.pop()] = 2
                stack.pop()
            elif state[candidate] == 1:
                cycle = path[path.index(candidate):] + [candidate]
                raise ManifestError(
                    "Import cycle detected: " + " -> ".join(cycle)
                )
            elif state[candidate] == 0:
                state[candidate] = 1
                path.append(candidate)
                stack.append(iter(parents[candidate]))


def _status(
    name: str,
    md5: str,
    previous: dict[str, ManifestNode],
) -> Literal["new", "clean", "changed"]:
    prior = previous.get(name)
    if prior is None:
        return "new"
    return "clean" if prior.md5 == md5 else "changed"


def build_manifest(
    project_root: Path,
    config: ProjectConfig,
    previous: Manifest | None = None,
) -> Manifest:
    """Scan every configured module and assemble the project DAG.

    Computes MD5 fingerprints, parses imports, resolves them to nodes,
    checks for cycles, and diffs against `previous` (when given) to
    assign each node a `new` / `clean` / `changed` status. No I/O side
    effects beyond reading the source files.
    """
    scanned: dict[str, _Facts] = {}
    stem_index: dict[str, list[str]] = {}

    for module_name in sorted(config.modules):
        module_dir = config.module_path(project_root, module_name)
        for relative in scan_module(module_dir):
            node_name = f"{module_name}.{_dotted_stem(relative)}"
            source = module_dir / relative
            try:
                data = source.read_bytes()
            except OSError as exc:
                raise ManifestError(f"Could not read {source}: {exc}") from exc
            try:
                path_in_project = source.relative_to(project_root)
            except ValueError as exc:
                raise ManifestError(
                    f"Module {module_name!r} source directory is outside the "
                    f"project root: {module_dir}"
                ) from exc
            scanned[node_name] = _Facts(
                name=node_name,
                module=module_name,
                path=path_in_project.as_posix(),
                dotted_stem=_dotted_stem(relative),
                md5=hashlib.md5(data).hexdigest(),
                imports=parse_imports(data.decode("utf-8", errors="replace")),
            )
            stem_index.setdefault(_dotted_stem(relative), []).append(node_name)

    parents: dict[str, set[str]] = {name: set() for name in scanned}
    for node in scanned.values():
        for imported in node.imports:
            resolved = _resolve_import(node, imported, stem_index, scanned)
            if resolved is not None:
                parents[node.name].add(resolved)

    children: dict[str, set[str]] = {name: set() for name in scanned}
    for name, node_parents in parents.items():
        for parent in node_parents:
            children[parent].add(name)

    parent_lists = {name: sorted(node_parents) for name, node_parents in parents.items()}
    _detect_cycle(parent_lists)

    now = datetime.now(timezone.utc)
    previous_nodes = previous.by_name() if previous else {}
    nodes = []
    for name, facts in sorted(scanned.items()):
        # Unchanged files carry their previous extraction data forward, so
        # they are not re-extracted (plan §3's incremental promise). A
        # persisted manifest only ever contains valid extraction data:
        # compile saves nothing unless every node extracted cleanly.
        prior = previous_nodes.get(name)
        carry = prior is not None and prior.md5 == facts.md5
        nodes.append(
            ManifestNode(
                name=facts.name,
                module=facts.module,
                path=facts.path,
                imports=facts.imports,
                parents=parent_lists[name],
                children=sorted(children[name]),
                md5=facts.md5,
                status=_status(name, facts.md5, previous_nodes),
                declarations=list(prior.declarations) if carry else [],
                last_checked=now,
            )
        )
    return Manifest(version=MANIFEST_VERSION, generated_at=now, nodes=nodes)


def _stem_matches(target: str, module_name: str, known: set[str]) -> bool:
    """Whether a target's `<file>.<declaration>` prefix names a known node.

    The file stem is matched greedily: for `Utils.Basic.thm` the stems
    `Utils.Basic` and `Utils` are tried, longest first.
    """
    parts = target.split(".")
    for split in range(len(parts) - 1, 0, -1):
        if f"{module_name}.{'.'.join(parts[:split])}" in known:
            return True
    return False


def check_targets(config: ProjectConfig, manifest: Manifest) -> None:
    """Verify that every configured target's file stem was actually scanned.

    Declaration-level validation is not possible until declarations are
    extracted from the sources; only the file component is checked here.
    """
    by_module: dict[str, set[str]] = {}
    for node in manifest.nodes:
        by_module.setdefault(node.module, set()).add(node.name)

    for module_name, module in config.modules.items():
        known = by_module.get(module_name, set())
        for target in module.targets:
            if not _stem_matches(target, module_name, known):
                raise ManifestError(
                    f"Target '{target}' of module {module_name!r} refers to a "
                    "file that was not found in the module's source directory."
                )


def topological_order(nodes: list[ManifestNode]) -> list[ManifestNode]:
    """Order `nodes` dependencies-first (plan §6's flattening order).

    Parents outside the selected set are treated as satisfied — a filtered
    view stays well-ordered without pulling its dependencies in. The
    manifest DAG is acyclic (validated at build time), so the loop always
    makes progress.
    """
    selected = {node.name for node in nodes}
    remaining = sorted(nodes, key=lambda node: node.name)
    emitted: list[ManifestNode] = []
    emitted_names: set[str] = set()
    while remaining:
        progress = False
        for node in list(remaining):
            if all(parent in emitted_names for parent in node.parents if parent in selected):
                remaining.remove(node)
                emitted.append(node)
                emitted_names.add(node.name)
                progress = True
        if not progress:  # pragma: no cover — DAG is cycle-free by construction
            emitted.extend(remaining)
            break
    return emitted
