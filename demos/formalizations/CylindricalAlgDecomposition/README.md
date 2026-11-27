# Collins CAD formalization

Lean 4 / Mathlib formalization of George E. Collins' cylindrical algebraic decomposition algorithm. The source PDF and `docs/` reference material are local-only, ignored, and not committed.

## Modules

- `Algebra` → `CollinsCAD/Algebra/`
- `Analysis` → `CollinsCAD/Analysis/`
- `CAD` → `CollinsCAD/CAD/`
- `Logic` → `CollinsCAD/Logic/`

Imports use `Algebra.*`, `Analysis.*`, `CAD.*`, and `Logic.*`; the Lean namespace remains `CollinsCAD` for CAD-specific declarations, with first-order language declarations in `FirstOrder.Language`.

## Current coverage

Clusters A–F are implemented and verified: reducta and variable splitting, subresultants and Collins Theorems 2–3, root continuity, Theorem 1, Collins projection, effective reducta, Collins Theorems 4 and 5, fundamental lifting, cylindrical cell trees, DECOMP, Thom's lemma, augmented projection, DEFINE, first-order ordered-ring logic, EVAL, ELIM, and quantifier elimination. The lifting API includes an explicit ordered continuous family whose range is exactly the union of factor-root sets, together with a per-factor vanishing dichotomy. `CAD/ZeroFiber.lean` filters arbitrary input families into retained factors with nowhere-zero fibres and excluded factors that vanish identically on the base set.

Cluster E exports `cad_decomp_exists`, `exists_augmented_cad`, `thom_lemma_univariate`, `cad_define_cell_formula`, and `cad_define_exists`. CAD levels use List-based cells and cylinders with explicit parent-to-child maps; cells carry connected carrier sets and sample points. DEFINE uses finite conjunctions of polynomial sign conditions. `CAD/Integrality.lean` proves that the DEFINE support envelope preserves integer coefficients, and `CAD/Structure.lean` exports direct child lookup, fibre coverage, nonemptiness, and projection APIs.

Cluster F defines the primitive strict-order language `FirstOrder.Language.orderedRing`, realizes it on `ℝ`, and translates ordered-ring terms to and from integer multivariate polynomials with realization preservation. `Logic/AtomPolys.lean` and `Logic/Evaluation.lean` extract finite atom support and prove quantifier-free truth is constant on invariant cells. `Logic/QuantifierStep.lean` evaluates `∀` and `∃` as finite conjunctions/disjunctions of child-cell sample truths. `Logic/SignFormula.lean`, `Logic/Prefix.lean`, `Logic/ElimStep.lean`, and `Logic/Elim.lean` translate DEFINE sign formulas, descend augmented CAD provenance through a prenex prefix, construct the accepting-cell disjunction, and prove `logic_elim_prenex`, `rcf_quantifier_elimination`, and `logic_elim_main`.

## Development

There is no local Lean toolchain. `axbt` submits self-contained payloads to the Axle API.

```sh
uv run axbt compile
uv run axbt check -s Algebra.GcdDegree.psc_ne_zero_of_gcd_eq
uv run axbt verify -s Algebra.GcdDegree.psc_ne_zero_of_gcd_eq
uv run axbt check -s CAD.Define
uv run axbt check -s Logic.Elim
uv run axbt build
```

`axbt build` is the finish line: it runs both the check and kernel-verification tiers.
