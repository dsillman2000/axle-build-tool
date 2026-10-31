"""Resolution of `--select` selectors against the manifest (plan §6).

A selector is dot-separated and resolved against the manifest:

- `<module>` — a whole module (every file in the module, dependencies
  included).
- `<module>.<file stem>[.<declaration>]` — the file stem is matched
  **greedily** (stems may themselves contain dots for nested files); any
  remainder is the declaration name, which may also contain dots, since
  Lean declaration names do.
"""

from __future__ import annotations

from dataclasses import dataclass

from axle_build_tool.config import ProjectConfig
from axle_build_tool.manifest import Manifest, ManifestNode
from axle_build_tool.payloads import compiled_filename, dotted_stem_of


class SelectionError(Exception):
    """Raised when a `--select` value does not resolve against the manifest."""


@dataclass(frozen=True)
class Selection:
    """A resolved selection.

    `node_name` is `None` for a module-wide selection; `declaration` is
    `None` for module- and file-wide selections.
    """

    module: str
    node_name: str | None = None
    declaration: str | None = None

    @property
    def compiled_filename(self) -> str:
        """The persisted payload filename for this selection."""
        if self.node_name is None:
            return compiled_filename(self.module)
        node_stem = self.node_name[len(self.module) + 1:]
        return compiled_filename(self.module, node_stem)

    def payload_nodes(self, manifest: Manifest) -> list[ManifestNode]:
        """The manifest nodes whose sources make up this selection's payload."""
        by_name = manifest.by_name()
        if self.node_name is None:
            return sorted(
                (node for node in by_name.values() if node.module == self.module),
                key=lambda node: node.name,
            )
        return [by_name[self.node_name]]


def resolve_selection(
    selector: str,
    config: ProjectConfig,
    manifest: Manifest,
) -> Selection:
    """Resolve a `--select` selector against the project manifest.

    Raises `SelectionError` with an actionable message if the module, file
    stem, or declaration does not resolve.
    """
    parts = selector.split(".")
    module = parts[0]
    if module not in config.modules:
        raise SelectionError(
            f"Unknown module {module!r} in selection {selector!r}. Modules "
            f"defined in axbt_project.yml: {', '.join(sorted(config.modules))}."
        )

    by_name = manifest.by_name()
    module_nodes = {
        node.name: node for node in by_name.values() if node.module == module
    }
    if not module_nodes:
        raise SelectionError(
            f"Selection {selector!r}: module {module!r} has no .lean files."
        )

    if len(parts) == 1:
        return Selection(module=module)

    remaining = parts[1:]
    longest_miss: tuple[ManifestNode, str] | None = None
    for take in range(len(remaining), 0, -1):
        candidate = f"{module}.{'.'.join(remaining[:take])}"
        node = module_nodes.get(candidate)
        if node is None:
            continue
        declaration = ".".join(remaining[take:]) or None
        if declaration is None:
            return Selection(module=module, node_name=candidate)
        extracted = sorted({decl.name for decl in node.declarations})
        if declaration in extracted:
            return Selection(module=module, node_name=candidate, declaration=declaration)
        # Ergonomic extension of §6's exact match: a remainder that names a
        # declaration by unique suffix (e.g. `M.Utils.Basic.x` for the
        # declaration `Utils.Basic.x` in `Utils/Basic.lean`).
        suffix_matches = [name for name in extracted if name.endswith("." + declaration)]
        if len(suffix_matches) == 1:
            return Selection(
                module=module, node_name=candidate, declaration=suffix_matches[0]
            )
        if len(suffix_matches) > 1:
            raise SelectionError(
                f"Selection {selector!r}: declaration {declaration!r} is "
                f"ambiguous in {node.path}; it matches: "
                f"{', '.join(suffix_matches)}."
            )
        # The stem matched but the remainder isn't an extracted declaration;
        # remember the longest-stem miss for the error message, and let a
        # shorter stem try (the remainder may be part of a namespaced
        # declaration name instead).
        if longest_miss is None:
            longest_miss = (node, declaration)

    if longest_miss is not None:
        node, declaration = longest_miss
        extracted = {decl.name for decl in node.declarations}
        if not extracted:
            raise SelectionError(
                f"Selection {selector!r}: no declarations were extracted "
                f"from {node.path}; run `axbt compile` first."
            )
        raise SelectionError(
            f"Selection {selector!r}: declaration {declaration!r} not "
            f"found in {node.path}. Extracted declarations: "
            f"{', '.join(sorted(extracted))}."
        )

    stems = sorted(dotted_stem_of(n) for n in module_nodes.values())
    raise SelectionError(
        f"Selection {selector!r}: no file stem matches "
        f"{'.'.join(remaining)!r} in module {module!r}. "
        f"File stems: {', '.join(stems)}."
    )
