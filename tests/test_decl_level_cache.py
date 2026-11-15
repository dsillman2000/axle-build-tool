"""Tests for declaration-level incremental caching (v0.2.0)."""

from __future__ import annotations

from pathlib import Path

from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.manifest import (
    ExtractedDecl,
    Manifest,
    ManifestNode,
    compute_ambient_hash,
    compute_decl_hashes,
    decl_closure_signature,
)
from conftest import make_document

runner = CliRunner()


def _make_node(
    name: str, source: str, decls: list[ExtractedDecl], parents: list[str] | None = None
) -> ManifestNode:
    lines = source.splitlines()
    hashed = []
    for d in decls:
        sh, bh = compute_decl_hashes(lines, d)
        hashed.append(d.model_copy(update={"sig_hash": sh, "body_hash": bh}))
    ah = compute_ambient_hash(lines, hashed)
    return ManifestNode(
        name=name,
        module="M",
        path=f"{name.replace('.', '/')}.lean",
        parents=parents or [],
        md5="0" * 32,
        status="clean",
        declarations=hashed,
        ambient_hash=ah,
    )


def test_comment_and_unrelated_proof_edits_preserve_decl_signatures() -> None:
    from datetime import datetime, timezone

    now = datetime.now(timezone.utc)
    a0 = "def d_a : Nat := 1\ntheorem a : d_a = 1 := rfl\n"
    b0 = "import A\ntheorem b_used : d_a = 1 := a\ntheorem b_unused : 1 = 1 := rfl\n"
    c0 = "import B\ntheorem c : d_a = 1 := b_used\n"

    def build(a_src: str, b_src: str, c_src: str) -> dict[str, str]:
        a_off = 1 if a_src.startswith("--") or a_src.startswith("open ") else 0
        n_a = _make_node("M.A", a_src, [
            ExtractedDecl(name="d_a", kind="def", is_sorry=False, line_pos=1 + a_off, end_line_pos=1 + a_off, signature="def d_a : Nat"),
            ExtractedDecl(name="a", kind="theorem", is_sorry=False, line_pos=2 + a_off, end_line_pos=2 + a_off, signature="theorem a : d_a = 1", dependencies=["d_a"]),
        ])
        n_b = _make_node("M.B", b_src, [
            ExtractedDecl(name="b_used", kind="theorem", is_sorry=False, line_pos=2, end_line_pos=2, signature="theorem b_used : d_a = 1", dependencies=["a", "d_a"]),
            ExtractedDecl(name="b_unused", kind="theorem", is_sorry=False, line_pos=3, end_line_pos=3, signature="theorem b_unused : 1 = 1"),
        ], parents=["M.A"])
        n_c = _make_node("M.C", c_src, [
            ExtractedDecl(name="c", kind="theorem", is_sorry=False, line_pos=2, end_line_pos=2, signature="theorem c : d_a = 1", dependencies=["b_used", "d_a"]),
        ], parents=["M.B"])
        manifest = Manifest(generated_at=now, nodes=[n_a, n_b, n_c])
        return {
            d.name: decl_closure_signature(n, d, manifest, "lean-4.35.0", {})
            for n in manifest.nodes
            for d in n.declarations
        }

    base = build(a0, b0, c0)
    # Comment edit in A.lean -> 0 invalidations
    assert build("-- comment\n" + a0, b0, c0) == base
    # Proof edit in unrelated b_unused -> only b_unused invalidates
    s_un = build(a0, b0.replace("rfl\n", "by rfl\n", 1), c0)
    assert {k for k in base if s_un[k] != base[k]} == {"b_unused"}
    # Proof edit in upstream theorem a -> only a invalidates (proof irrelevance)
    s_a = build(a0.replace(":= rfl", ":= by rfl"), b0, c0)
    assert {k for k in base if s_a[k] != base[k]} == {"a"}
    # Body edit in upstream def d_a -> d_a, a, b_used, c invalidate; b_unused stays cached
    s_def = build(a0.replace(":= 1", ":= 2"), b0, c0)
    assert {k for k in base if s_def[k] != base[k]} == {"d_a", "a", "b_used", "c"}
    # Ambient edit (`open Nat`) in A.lean -> A + dependents invalidate; b_unused stays cached
    s_open = build("open Nat\n" + a0, b0, c0)
    assert {k for k in base if s_open[k] != base[k]} == {"d_a", "a", "b_used", "c"}
