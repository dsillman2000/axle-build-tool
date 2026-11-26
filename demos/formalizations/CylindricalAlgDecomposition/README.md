# Collins CAD formalization

Lean 4 / Mathlib formalization of George E. Collins' cylindrical algebraic decomposition algorithm. The source PDF and `docs/` reference material are local-only, ignored, and not committed.

## Modules

- `Algebra` → `CollinsCAD/Algebra/`
- `Analysis` → `CollinsCAD/Analysis/`

Imports use `Algebra.*` and `Analysis.*`; the Lean namespace remains `CollinsCAD`.

## Current coverage

Clusters A–C are implemented and verified: reducta and variable splitting, subresultants and Collins Theorems 2–3, root continuity, local root functions, and Theorem 1 for polynomial families and multivariate fibres. Reusable APIs include the UFD-valued Theorem 2, a shared Vieta-subsequence helper, local complex root-multiplicity constancy, nonzero constant-fibre delineability, and the reductum/fibre bridge.

## Development

There is no local Lean toolchain. `axbt` submits self-contained payloads to the Axle API.

```sh
uv run axbt compile
uv run axbt check -s Algebra.GcdDegree.psc_ne_zero_of_gcd_eq
uv run axbt verify -s Algebra.GcdDegree.psc_ne_zero_of_gcd_eq
uv run axbt build
```

`axbt build` is the finish line: it runs both the check and kernel-verification tiers.
