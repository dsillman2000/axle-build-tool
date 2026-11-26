# Collins CAD formalization

Lean 4 / Mathlib formalization of George E. Collins' cylindrical algebraic decomposition algorithm. The source PDF and `docs/` reference material are local-only, ignored, and not committed.

## Modules

- `Algebra` → `CollinsCAD/Algebra/`
- `Analysis` → `CollinsCAD/Analysis/`
- `CAD` → `CollinsCAD/CAD/`

Imports use `Algebra.*`, `Analysis.*`, and `CAD.*`; the Lean namespace remains `CollinsCAD`.

## Current coverage

Clusters A–E are implemented and verified: reducta and variable splitting, subresultants and Collins Theorems 2–3, root continuity, Theorem 1, Collins projection, effective reducta, Collins Theorems 4 and 5, fundamental lifting, cylindrical cell trees, DECOMP, Thom's lemma, augmented projection, and DEFINE. The lifting API includes an explicit ordered continuous family whose range is exactly the union of factor-root sets, together with a per-factor vanishing dichotomy. `CAD/ZeroFiber.lean` filters arbitrary input families into retained factors with nowhere-zero fibres and excluded factors that vanish identically on the base set.

Cluster E exports `cad_decomp_exists`, `exists_augmented_cad`, `thom_lemma_univariate`, `cad_define_cell_formula`, and `cad_define_exists`. CAD levels use List-based cells and cylinders with explicit parent-to-child maps; cells carry connected carrier sets and sample points. DEFINE uses finite conjunctions of polynomial sign conditions, with first-order formula syntax deferred to Cluster F.

## Development

There is no local Lean toolchain. `axbt` submits self-contained payloads to the Axle API.

```sh
uv run axbt compile
uv run axbt check -s Algebra.GcdDegree.psc_ne_zero_of_gcd_eq
uv run axbt verify -s Algebra.GcdDegree.psc_ne_zero_of_gcd_eq
uv run axbt check -s CAD.Define
uv run axbt build
```

`axbt build` is the finish line: it runs both the check and kernel-verification tiers.
