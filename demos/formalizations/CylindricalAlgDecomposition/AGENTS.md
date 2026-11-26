# Cylindrical algebraic decomposition formalization

Goal: formalize George E. Collins' quantifier-elimination algorithm for real closed fields
("Quantifier Elimination for Real Closed Fields by Cylindrical Algebraic Decomposition", 1975)
in Lean 4 / Mathlib, following the dependency-ordered blueprint produced by Gemini/Neon.

There is no local Lean install. All proof work goes through `axbt`, which submits
self-contained payloads to the Axle API. Requires `AXLE_API_KEY` in the environment.

## Layout

The PDF and everything under `docs/` are local-only reference material. They are ignored by Git and are not part of the demo branch.

- `3-540-07407-4_17.pdf` — the original 50-page paper (scanned typewritten pages).
- `docs/page01.md` … `docs/page50.md` — Markdown OCR transcriptions of the paper, one file per
  PDF page. They were produced page-by-page in the Gemini chat and saved verbatim except for
  attachment-name artifacts (`cad-pageN.jpg`). Page 48 and 50 are structured bibliography
  extractions rather than strict verbatim transcriptions. "discoverd" on page 1 is faithful to
  the scan and must not be "corrected".
- `docs/blueprint.md` — the Gemini/Neon blueprint: formal statement sketches, a DAG of lemmas
  with `mathlib_status`/`tactic_hint`/`risk`, module layout, gap analysis. This is the roadmap.
- `docs/alphaxiv-summary.md` — a high-level summary of the paper, useful for orientation.
- `docs/collins-cad-brief.md` — the condensed mathematical brief fed to Neon to obtain the
  blueprint; use it when the full transcription is too large to hand to a model.
- `axbt_project.yml` — project root. Modules `Algebra`, `Analysis`, and `CAD` live in
  `CollinsCAD/Algebra/`, `CollinsCAD/Analysis/`, and `CollinsCAD/CAD/`. Environment is pinned
  to `lean-4.36.0`; API timeout is 600 s (some proofs are expensive).
- `.axbt/` — axbt's offline cache and failure artifacts (gitignore it). `manifest.json` holds
  declaration stamps; `failed/` holds exact submitted payloads and source maps.
- `CollinsCAD/Algebra/` — algebraic Lean sources, one file per concept; import siblings by
  file stem (e.g. `import Algebra.Subresultant`).
- `CollinsCAD/Analysis/` — analytic Lean sources; use `Analysis.*` for sibling imports and
  `Algebra.*` for algebraic dependencies. The Lean namespace remains `CollinsCAD`.
- `CollinsCAD/CAD/` — projection and lifting sources; use `CAD.*` for sibling imports and
  `Analysis.*` / `Algebra.*` for upstream dependencies.

## Development process

1. Read the relevant `docs/pageNN.md` and the corresponding blueprint node before writing Lean.
2. Write small single-purpose files with LaTeX doc comments aimed at mathematicians.
3. Iterate with `axbt compile` then `axbt check -s <Module.File.decl>`; use `axbt verify -s …`
   for kernel-level verification of finished proofs. Do not rely on `check` alone — a `sorry`
   typechecks but does not verify. `axbt build` is the finish line (check pass then verify pass).
4. Do not reflexively use `--force`/`--full-refresh`; incremental compilation and
   declaration-level caching re-judge only what changed. For unfinished upstream declarations,
   use `axbt build --sorry <upstream-file>` or `verify --permitted-sorries <selector>`.
5. Some heavy declarations use `set_option maxHeartbeats N in` immediately before the doc
   comment. Keep the option before the docstring so axbt's declaration splitter stays happy.
6. On a FAIL, read the named `.axbt/failed/<id>.lean` payload and its `.map.json` before
   rebuilding from source; positions in the report refer to that exact payload.

## Status

Clusters A, B, C, and D are implemented and verified. `Analysis/Theorem1Mv.lean`
specializes Collins' Theorem 1 to normalized multivariate fibres, and `CAD/`
implements projection definitions, effective reducta, Collins Theorems 4 and 5,
pairwise branch coincidence, and fundamental lifting. Remaining blueprint work:
cluster E (CAD construction, DECOMP/DEFINE) and cluster F (logic/EVAL/ELIM).

### Cluster D notes

- `CAD/ProjectionDef.lean` defines `reductaSet`, `projL`, `projS1`, `projS2`, and
  `collinsProj`. Nonzero constant reducta contribute to `projL`; this is necessary
  for `projection_effective_reductum`.
- `CAD/EffectiveReductum.lean` proves the effective-reductum theorem.
  `CAD/GcdDegreeConstancy.lean` transports the PSC zero/nonzero pattern across a
  projection-invariant base set, including the `j < min(deg B₁, deg B₂)` boundary.
- `CAD/Theorem4.lean` handles nonzero constant fibres explicitly and derives the
  positive-degree case from GCD-degree constancy and Collins Theorem 3.
- `CAD/CommonRoots.lean`, `CAD/LocalRootData.lean`, `CAD/JointRootData.lean`, and
  `CAD/JointGcdDegree.lean` prove the local common-root multiplicity-sum formula.
  `CAD/Pairwise.lean` turns constant GCD degree into clopen branch coincidence.
- `CAD/Lifting.lean` exports `projection_fundamental_lifting`: an explicit finite,
  strictly ordered continuous family covering exactly the union of factor roots.
  The theorem assumes every factor fibre is nonzero on the base set; globally
  nonzero polynomials can still have identically zero fibres.

### Cluster C notes

- `Analysis/Delineability.lean` defines `fiberPoly`, `SignInvariantPoly`, `SignInvariant`,
  `IsRealDelineable`, and `IsDelineable`. `SignInvariantPoly.of_connected_ne_zero`
  derives invariance on a connected set from nonvanishing by the intermediate value theorem.
- `Analysis/RootContinuity.lean` proves `cauchy_root_bound` (roots of a monic degree-$d$
  polynomial satisfy $\|z\| \le \max 1 \sum_{k<d}\|P_k\|$), the coefficient-vector helpers
  `polyOfCoeffs`/`coeff_polyOfCoeffs`/`polyOfCoeffs_self`, and the shared
  `exists_vieta_subsequence_of_coeff_close` helper. The helper enumerates roots via
  `roots.toList`/`List.ofFn`, bounds them by the Cauchy bound, extracts a convergent
  subsequence with `IsCompact.tendsto_subseq`, and identifies the limit using
  `Polynomial.funext` (evaluation convergence avoids needing continuity of the Vieta map).
  Both `exists_root_near_of_coeff_close` and `roots_count_in_ball_eq_of_coeff_close`
  reuse this core.
  `roots_persist_near_of_coeff_close` extends this to all distinct roots at once by
  finite induction over `roots.toFinset` with a minimum of the individual moduli.
- `roots_count_in_ball_eq_of_coeff_close` is the exact node-20 statement: the number of
  roots (with multiplicity) in a disc around one distinct root is preserved. It reuses
  the compactness core and then identifies the limit multiset via `Fin.univ_val_map`
  and `Polynomial.roots_multiset_prod_X_sub_C`.
- `Analysis/LocalRoots.lean` adds `exists_separation_radius`, `eval_eq_sum_fin`,
  `evalFin`, and `continuous_unique_root_in_ball`: a root selected uniquely from an
  isolated disc varies continuously along a continuous coefficient family. The proof
  uses `Filter.tendsto_of_subseq_tendsto`, compactness of a bounded disc, and
  uniqueness via a separation radius. Writing the joint evaluation map as the named
  `evalFin` avoids a whnf loop with `Tendsto.comp` on an anonymous finite sum.
- `unique_root_in_ball_of_count` turns preserved disc counts plus constant distinct-root
  count into uniqueness of a root in each disc, using `Finset.card_biUnion` and
  disjointness of the discs; it also returns coverage of all roots by the discs.
  `locally_unique_roots_of_monic_family` combines this with coefficient continuity to
  produce an open neighbourhood of a base point where each disc has a unique root.
- `local_continuous_root_functions` and `local_real_root_functions` provide continuous
  root functions on a neighbourhood, with real centres giving real-valued functions;
  `conj_root_of_real_coeff` and `real_of_unique_root_in_real_ball` drive the partition.
  `rootMultiplicity_locally_constant_of_continuous_root_in_ball` exports local constancy
  of complex root multiplicities for reuse by projection arguments.
  `real_root_count_locally_constant` proves the number of distinct real roots is locally
  constant by a `Finset.card_bij` between the real roots at nearby points.
- `real_root_count_constant_on_preconnected` uses `IsLocallyConstant.iff_exists_open`
  and `IsLocallyConstant.apply_eq_of_preconnectedSpace` to obtain a single global `k`.
- `Analysis/Theorem1.lean` defines `ordered_real_root_functions_of_family` and
  `ordered_real_root_functions_with_multiplicity` using `Finset.orderEmbOfFin` on the
  real parts of the roots, `Finset.orderEmbOfFin_unique` to identify each global `f_i`
  with a local continuous branch, and `IsLocallyConstant` to transport multiplicities.
  `delineability_theorem_1_real` is the resulting family-version statement.
- `Analysis/Theorem1Mv.lean` specializes the family theorem to the normalized fibre
  polynomials of an `MvPolynomial` on a connected `S`. The fibre is scaled by the
  inverse of its leading coefficient; `rootMultiplicity_map_eq` transfers multiplicities
  from $\mathbb{R}$ to $\mathbb{C}$, and `Polynomial.roots_C_mul` makes the scaling
  invisible to roots. `delineability_theorem_1_real_mv` yields `IsRealDelineable P S`;
  `isRealDelineable_of_fiber_natDegree_eq_zero` handles nonzero constant fibres.
  `fiberPoly_eq_reductum_map_of_leadingCoeff_eq_zero` provides the reductum/fibre bridge
  needed by effective-reductum arguments.
- Next step: Cluster E (CAD construction, DECOMP/DEFINE).

### Cluster A notes

- `reductum` is iterated `eraseLead`; the degree/support bounds use `eraseLead_natDegree_lt_or_eraseLead_eq_zero` and `card_support_eraseLead`.
- `finLastEquiv` views $R[X_0,\ldots,X_r]$ as $R[X_0,\ldots,X_{r-1}][X]$ via
  `Fin (r+1) ≃ Option (Fin r)` and `MvPolynomial.optionEquivLeft`; `eval_last_comm` uses
  `MvPolynomial.optionEquivLeft_elim_eval` and `hom_eq_hom`.

### Cluster B notes

- Mathlib 4.36 has `Polynomial.resultant` but no subresultants, so `subresultantMatrix` and
  `psc` are defined locally as determinants of the explicit coefficient matrix.
- `coeffMap` is the linear map on `Polynomial.degreeLT` spaces sending $(u,v)$ to coefficients
  of $uA+vB$ in degrees $j,\ldots,m+n-j-1$; `coeffMap_toMatrix` identifies its matrix (in the
  `degreeLT.basisProd` / `Pi.basisFun` bases) with the transpose of `subresultantMatrix`.
- `psc_eq_zero_iff_exists_uv` is the kernel-to-Bézout bridge. It uses
  `Matrix.exists_vecMul_eq_zero_iff` rather than hand-built coefficient expansions.
- Collins Theorem 2 (`subresultant_deg_gcd_eq_least_nonzero_psc`) is proved from two
  directional lemmas: `psc_ne_zero_of_gcd_eq` and `psc_eq_zero_of_lt_gcd`. The coprime step
  uses Bézout (`EuclideanDomain.gcd_eq_gcd_ab`) rather than division APIs, which was much
  cheaper for the elaborator.
- Collins Theorem 3 (`roots_card_distinct_eq_sub_deg_gcd_deriv`) is proved over ℂ from root
  multiplicities, then mapped back from ℝ. `Multiset.toFinset_sum_count_eq` gives the sum of
  multiplicities; `Finset.sum_add_distrib` gives the cardinality identity without a brittle
  subtraction rewrite.
- The UFD/Gauss node (`subresultant_gauss_content_lift`) uses
  `IsLocalization.integerNormalization` and `IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`.
  `subresultant_deg_gcd_eq_least_nonzero_psc_ufd` composes this lift with the field-valued
  Theorem 2 and `psc_map` to export Collins Theorem 2 over a UFD.

### Mathlib API gotchas encountered

- Prefer `natDegree` over `WithBot` degree arithmetic; the latter needs instances that are
  awkward to synthesize.
- Current Mathlib uses generic `Finset.antidiagonal`; the old `Finset.Nat.mem_antidiagonal`
  path is not reliable. Use `Polynomial.coeff_X_pow_mul'` where possible.
- Big-operator notation here is `∑ x ∈ s, …` (with `open scoped BigOperators`); `∑ x in s` may
  not parse.
- `EuclideanDomain.gcd` and `GCDMonoid.gcd` are not definitionally the same in every theorem;
  `simpa`/`change` may be needed, and `EuclideanDomain.dvd_gcd` is the field-safe variant.
- `Polynomial.rootMultiplicity_pos` takes the nonzero proof as an explicit first argument;
  `Polynomial.degree_pos_of_root` plus `Polynomial.coe_lt_degree` converts to `natDegree`.

## External artifacts

The paper transcriptions and blueprint came from two Gemini sessions driven with the `browse`
CLI on the user's Brave browser:

- OCR Document Transcription Task: `https://gemini.google.com/app/8d9a1c6df42a20f2`
- Lean 4 Formalization Blueprint: `https://gemini.google.com/app/acdf77bc0815feec`

When requesting more transcriptions, render a page with `pdftoppm -r 200 -jpeg -singlefile`
and upload the image; use the response's Copy action to get clean Markdown.
