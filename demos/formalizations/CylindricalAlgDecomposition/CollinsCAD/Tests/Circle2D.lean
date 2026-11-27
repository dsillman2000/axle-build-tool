import Mathlib
import Tests.Parabola2D

/-!
# Nontrivial CAD test 3: unit circle $x_0^2 + x_1^2 - 1$

This file pins down the two-level cylindrical algebraic decomposition for the
unit circle $P(x_0, x_1) = x_0^2 + x_1^2 - 1 \in \mathbb{R}[x_0, x_1]$:
- projection to dimension $1$ produces leading coefficients $1$ and $x_0^2 - 1$
  together with the discriminant $4(x_0^2 - 1)$;
- the $1$-dimensional base decomposition of $\mathbb{R}^1$ around the two roots
  $-1 < 1$ of $x_0^2 - 1$ yields $5$ cells $(-\infty, -1)$, $\{-1\}$,
  $(-1, 1)$, $\{1\}$, and $(1, \infty)$ with sample points $-2, -1, 0, 1, 2$
  and alternating signs $+1, 0, -1, 0, +1$;
- lifting over those $5$ base cells yields $1 + 3 + 5 + 3 + 1 = 13$ cells in
  $\mathbb{R}^2$, including the $5$-cell cylinder over $(-1, 1)$ delineated by
  the lower and upper semicircle root branches
  $f_0(x_0) = -\sqrt{1 - x_0^2}$ and $f_1(x_0) = \sqrt{1 - x_0^2}$;
- quantifier elimination on $\exists x_1,\, x_0^2 + x_1^2 - 1 = 0$ produces a
  quantifier-free ordered-ring formula equivalent to $-1 \le x_0 \le 1$.
-/

open scoped FirstOrder.Language

namespace CollinsCAD

open Polynomial MvPolynomial FirstOrder FirstOrder.Language

/-- The base projection polynomial $Q(x_0) = x_0^2 - 1 \in \mathbb{R}[x_0]$. -/
noncomputable def circleBasePoly : MvPolynomial (Fin 1) ℝ :=
  MvPolynomial.X 0 ^ 2 - 1

/-- Evaluating $x_0^2 - 1$ at $a : \operatorname{Fin} 1 \to \mathbb{R}$ gives
    $a(0)^2 - 1$. -/
@[simp] theorem eval_circleBasePoly (a : Fin 1 → ℝ) :
    MvPolynomial.eval a circleBasePoly = a 0 ^ 2 - 1 := by
  simp [circleBasePoly]

/-- The unit-circle polynomial $P(x_0, x_1) = x_0^2 + x_1^2 - 1$. -/
noncomputable def circle2DPoly : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.X 1 ^ 2 + (MvPolynomial.X 0 ^ 2 - 1)

/-- Under `finLastEquiv`, $x_1^2 + (x_0^2 - 1)$ becomes
    $X^2 + C(x_0^2 - 1) \in \mathbb{R}[x_0][X]$. -/
theorem finLastEquiv_circle2DPoly :
    finLastEquiv ℝ 1 circle2DPoly =
      Polynomial.X ^ 2 + Polynomial.C circleBasePoly := by
  change finLastEquiv ℝ 1
      (MvPolynomial.X (Fin.last 1) ^ 2 +
        (MvPolynomial.X (Fin.castSucc 0) ^ 2 - 1)) =
    Polynomial.X ^ 2 + Polynomial.C (MvPolynomial.X 0 ^ 2 - 1)
  rw [map_add, map_sub, map_pow, map_pow, map_one, finLastEquiv_X_last,
    finLastEquiv_X_castSucc, ← Polynomial.C_pow, ← Polynomial.C_1,
    ← Polynomial.C_sub]

/-- The fibre polynomial of $x_1^2 + (x_0^2 - 1)$ over $a \in \mathbb{R}^1$ is
    $X^2 + C(a_0^2 - 1) \in \mathbb{R}[X]$. -/
theorem fiberPoly_circle2DPoly (a : Fin 1 → ℝ) :
    fiberPoly 1 circle2DPoly a = Polynomial.X ^ 2 + Polynomial.C (a 0 ^ 2 - 1) := by
  simp [fiberPoly, finLastEquiv_circle2DPoly]

/-- The degree of $X^2 + C(x_0^2 - 1)$ in the last variable is $2$. -/
theorem natDegree_circle2DLast :
    (Polynomial.X ^ 2 + Polynomial.C circleBasePoly).natDegree = 2 := by
  simp

/-- The leading coefficient of $X^2 + C(x_0^2 - 1)$ in the last variable is $1$. -/
theorem leadingCoeff_circle2DLast :
    (Polynomial.X ^ 2 + Polynomial.C circleBasePoly).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, natDegree_circle2DLast]
  simp

/-- The first three reducta of $X^2 + C(x_0^2 - 1)$ are $X^2 + C(x_0^2 - 1)$,
    $C(x_0^2 - 1)$, and $0$. -/
theorem reducta_circle2DPoly :
    reductum 0 (finLastEquiv ℝ 1 circle2DPoly) =
      Polynomial.X ^ 2 + Polynomial.C circleBasePoly ∧
    reductum 1 (finLastEquiv ℝ 1 circle2DPoly) =
      Polynomial.C circleBasePoly ∧
    reductum 2 (finLastEquiv ℝ 1 circle2DPoly) = 0 := by
  have h0 : reductum 0 (finLastEquiv ℝ 1 circle2DPoly) =
      Polynomial.X ^ 2 + Polynomial.C circleBasePoly := by
    rw [reductum_zero, finLastEquiv_circle2DPoly]
  have h1 : reductum 1 (finLastEquiv ℝ 1 circle2DPoly) =
      Polynomial.C circleBasePoly := by
    rw [reductum_succ, h0, eraseLead_eq_sub_leadingTerm,
      natDegree_circle2DLast, leadingCoeff_circle2DLast]
    simp
  have h2 : reductum 2 (finLastEquiv ℝ 1 circle2DPoly) = 0 := by
    rw [reductum_succ, h1, Polynomial.eraseLead_C]
  exact ⟨h0, h1, h2⟩

/-- The polynomial $x_0^2 - 1 \in \mathbb{R}[x_0]$ is nonzero. -/
theorem circleBasePoly_ne_zero : circleBasePoly ≠ 0 := by
  intro h0
  have hev := congrArg (MvPolynomial.eval (fun _ => (0 : ℝ))) h0
  simp [circleBasePoly] at hev

/-- Collins projection of $\{x_1^2 + (x_0^2 - 1)\}$ contains the leading
    coefficients $1$ and $x_0^2 - 1$ as well as the discriminant
    $4(x_0^2 - 1)$. -/
theorem collinsProj_circle2DPoly_members :
    psc (finLastEquiv ℝ 1 circle2DPoly)
      (finLastEquiv ℝ 1 circle2DPoly).derivative 0 = 4 * circleBasePoly ∧
    (1 : MvPolynomial (Fin 1) ℝ) ∈ collinsProj {circle2DPoly} ∧
    circleBasePoly ∈ collinsProj {circle2DPoly} ∧
    (4 * circleBasePoly : MvPolynomial (Fin 1) ℝ) ∈ collinsProj {circle2DPoly} := by
  have hderiv : (finLastEquiv ℝ 1 circle2DPoly).derivative =
      Polynomial.C 2 * Polynomial.X := by
    rw [finLastEquiv_circle2DPoly, derivative_X_sq_add_C]
  have hdegP : (finLastEquiv ℝ 1 circle2DPoly).natDegree = 2 := by
    rw [finLastEquiv_circle2DPoly, natDegree_circle2DLast]
  have hdegD : (finLastEquiv ℝ 1 circle2DPoly).derivative.natDegree = 1 := by
    rw [hderiv, Polynomial.natDegree_C_mul_X]
    norm_num
  have hpsc : psc (finLastEquiv ℝ 1 circle2DPoly)
      (finLastEquiv ℝ 1 circle2DPoly).derivative 0 = 4 * circleBasePoly := by
    rw [psc_eq_fixed_psc, hdegP, hdegD, finLastEquiv_circle2DPoly,
      derivative_X_sq_add_C, fixed_psc_X_sq_add_C_derivative]
    ring
  have hne0 : reductum 0 (finLastEquiv ℝ 1 circle2DPoly) ≠ 0 := by
    rw [reductum_zero]
    intro h0
    rw [h0] at hdegP
    simp at hdegP
  have hmem0 := reductum_mem_reductaSet (A := {circle2DPoly}) (by simp) hne0
  have hlc0 : (reductum 0 (finLastEquiv ℝ 1 circle2DPoly)).leadingCoeff = 1 := by
    rw [reducta_circle2DPoly.1, leadingCoeff_circle2DLast]
  have hne1 : reductum 1 (finLastEquiv ℝ 1 circle2DPoly) ≠ 0 := by
    rw [reducta_circle2DPoly.2.1]
    exact Polynomial.C_ne_zero.mpr circleBasePoly_ne_zero
  have hmem1 := reductum_mem_reductaSet (A := {circle2DPoly}) (by simp) hne1
  have hlc1 : (reductum 1 (finLastEquiv ℝ 1 circle2DPoly)).leadingCoeff =
      circleBasePoly := by
    rw [reducta_circle2DPoly.2.1, Polynomial.leadingCoeff_C]
  refine ⟨hpsc, ?_, ?_, ?_⟩
  · rw [← hlc0]
    exact leadingCoeff_mem_collinsProj hmem0
  · rw [← hlc1]
    exact leadingCoeff_mem_collinsProj hmem1
  · rw [reductum_zero] at hmem0
    rw [← hpsc]
    exact psc_self_derivative_mem_collinsProj hmem0 (by omega)

/-- The two ordered roots $-1 < 1$ of $x_0^2 - 1$ over `baseCell0`. -/
noncomputable def circleBaseRoots : RootFamily baseCell0.carrier where
  k := 2
  f := fun i _ => if i.val = 0 then -1 else 1
  continuous := fun _ => continuousOn_const
  ordered := by
    intro i j _ _ hij
    have hi : i.val = 0 := by omega
    have hj : j.val = 1 := by omega
    simp [hi, hj]

/-- The five 1D base cells for $x_0^2 - 1$:
    $(-\infty, -1)$, $\{-1\}$, $(-1, 1)$, $\{1\}$, and $(1, \infty)$. -/
noncomputable def circleBaseCell0 : Cell 1 :=
  Cell.lower baseCell0 (fun _ => -1) continuousOn_const

noncomputable def circleBaseCell1 : Cell 1 :=
  Cell.graph baseCell0 (fun _ => -1) continuousOn_const

noncomputable def circleBaseCell2 : Cell 1 :=
  Cell.bounded baseCell0 (fun _ => -1) (fun _ => 1)
    continuousOn_const continuousOn_const (fun _ _ => by norm_num)

noncomputable def circleBaseCell3 : Cell 1 :=
  Cell.graph baseCell0 (fun _ => 1) continuousOn_const

noncomputable def circleBaseCell4 : Cell 1 :=
  Cell.upper baseCell0 (fun _ => 1) continuousOn_const

/-- Lifting `baseCell0` by `circleBaseRoots` produces the $5$-element list
    `[circleBaseCell0, circleBaseCell1, circleBaseCell2, circleBaseCell3, circleBaseCell4]`. -/
theorem liftCells_circleBaseRoots :
    liftCells baseCell0 circleBaseRoots =
      [circleBaseCell0, circleBaseCell1, circleBaseCell2,
       circleBaseCell3, circleBaseCell4] := by
  unfold liftCells circleBaseRoots
  dsimp only
  rw [liftCellsAux_succ_of_pos _ 1 _ _ _ (by omega), liftCellsAux_one]
  rfl

/-- The five base cells have sample points $-2, -1, 0, 1, 2$. -/
theorem circleBase_samples :
    circleBaseCell0.sample 0 = -2 ∧
    circleBaseCell1.sample 0 = -1 ∧
    circleBaseCell2.sample 0 = 0 ∧
    circleBaseCell3.sample 0 = 1 ∧
    circleBaseCell4.sample 0 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change @Fin.snoc 0 (fun _ => ℝ) baseCell0.sample ((-1 : ℝ) - 1) (Fin.last 0) = -2
    rw [Fin.snoc_last]; ring
  · change @Fin.snoc 0 (fun _ => ℝ) baseCell0.sample (-1 : ℝ) (Fin.last 0) = -1
    rw [Fin.snoc_last]
  · change @Fin.snoc 0 (fun _ => ℝ) baseCell0.sample (((-1 : ℝ) + 1) / 2) (Fin.last 0) = 0
    rw [Fin.snoc_last]; ring
  · change @Fin.snoc 0 (fun _ => ℝ) baseCell0.sample (1 : ℝ) (Fin.last 0) = 1
    rw [Fin.snoc_last]
  · change @Fin.snoc 0 (fun _ => ℝ) baseCell0.sample ((1 : ℝ) + 1) (Fin.last 0) = 2
    rw [Fin.snoc_last]; ring

/-- The base projection polynomial $x_0^2 - 1$ is sign-invariant on each of the
    five 1D base cells, taking signs $+1, 0, -1, 0, +1$ at their sample
    points. -/
theorem circleBase_cells_signInvariant :
    ∀ c ∈ liftCells baseCell0 circleBaseRoots,
      SignInvariant {circleBasePoly} c.carrier := by
  rw [liftCells_circleBaseRoots]
  intro c hc P hP
  have hPeq : P = circleBasePoly := Finset.mem_singleton.mp hP
  subst P
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · refine ⟨1, ?_⟩
    intro z hz
    have hlt : z 0 < -1 := (Cell.mem_lower.mp hz).2
    rw [eval_circleBasePoly, sign_eq_one_iff]
    nlinarith
  · refine ⟨0, ?_⟩
    intro z hz
    have heq : z 0 = -1 := (Cell.mem_graph.mp hz).2
    rw [eval_circleBasePoly, heq]
    norm_num
  · refine ⟨-1, ?_⟩
    intro z hz
    have hb := Cell.mem_bounded.mp hz
    have h1 : -1 < z 0 := hb.2.1
    have h2 : z 0 < 1 := hb.2.2
    rw [eval_circleBasePoly, sign_eq_neg_one_iff]
    nlinarith
  · refine ⟨0, ?_⟩
    intro z hz
    have heq : z 0 = 1 := (Cell.mem_graph.mp hz).2
    rw [eval_circleBasePoly, heq]
    norm_num
  · refine ⟨1, ?_⟩
    intro z hz
    have hgt : 1 < z 0 := (Cell.mem_upper.mp hz).2
    rw [eval_circleBasePoly, sign_eq_one_iff]
    nlinarith

/-- On the open interval cell `circleBaseCell2` ($-1 < x_0 < 1$), the two
    continuous semicircle root functions
    $f_0(a) = -\sqrt{1 - a_0^2}$ and $f_1(a) = \sqrt{1 - a_0^2}$ form a
    strictly ordered `RootFamily`. -/
noncomputable def circleInteriorRoots : RootFamily circleBaseCell2.carrier where
  k := 2
  f := fun i a =>
    if i.val = 0 then -Real.sqrt (1 - a 0 ^ 2) else Real.sqrt (1 - a 0 ^ 2)
  continuous := by
    intro i
    have hrad : Continuous (fun a : Fin 1 → ℝ => Real.sqrt (1 - a 0 ^ 2)) :=
      Real.continuous_sqrt.comp
        (continuous_const.sub ((continuous_apply 0).pow 2))
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceIte]
      exact hrad.neg.continuousOn
    · simp only [hi, ↓reduceIte]
      exact hrad.continuousOn
  ordered := by
    intro i j a ha hij
    have hi : i.val = 0 := by omega
    have hj : j.val = 1 := by omega
    simp only [hi, hj, ↓reduceIte, one_ne_zero]
    have hb := Cell.mem_bounded.mp ha
    have h1 : -1 < a 0 := hb.2.1
    have h2 : a 0 < 1 := hb.2.2
    have hpos : 0 < Real.sqrt (1 - a 0 ^ 2) :=
      Real.sqrt_pos.mpr (by nlinarith)
    linarith

/-- Both semicircle branches $f_0(a) = -\sqrt{1 - a_0^2}$ and
    $f_1(a) = \sqrt{1 - a_0^2}$ are exact roots of the fibre polynomial
    `fiberPoly 1 circle2DPoly a` over every point $a \in (-1, 1)$. -/
theorem circleInteriorRoots_are_fiber_roots (i : Fin 2) (a : Fin 1 → ℝ)
    (ha : a ∈ circleBaseCell2.carrier) :
    Polynomial.eval (circleInteriorRoots.f i a)
      (fiberPoly 1 circle2DPoly a) = 0 := by
  have hb := Cell.mem_bounded.mp ha
  have h1 : -1 < a 0 := hb.2.1
  have h2 : a 0 < 1 := hb.2.2
  have hnonneg : 0 ≤ 1 - a 0 ^ 2 := by nlinarith
  have hsq : Real.sqrt (1 - a 0 ^ 2) ^ 2 = 1 - a 0 ^ 2 :=
    Real.sq_sqrt hnonneg
  rw [fiberPoly_circle2DPoly]
  fin_cases i
  · change Polynomial.eval (-Real.sqrt (1 - a 0 ^ 2))
      (Polynomial.X ^ 2 + Polynomial.C (a 0 ^ 2 - 1)) = 0
    simp [hsq]
  · change Polynomial.eval (Real.sqrt (1 - a 0 ^ 2))
      (Polynomial.X ^ 2 + Polynomial.C (a 0 ^ 2 - 1)) = 0
    simp [hsq]

/-- The lifted cylinder over $(-1, 1)$ has $5$ cells, and across all $5$ base
    cells the 2D CAD for the unit circle has $1 + 3 + 5 + 3 + 1 = 13$ cells. -/
theorem circle2D_cell_counts :
    (liftCells circleBaseCell0
      ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩).length = 1 ∧
    (liftCells circleBaseCell1
      ⟨1, fun _ _ => 0, fun _ => continuousOn_const,
       fun _ _ _ _ hij => by omega⟩).length = 3 ∧
    (liftCells circleBaseCell2 circleInteriorRoots).length = 5 ∧
    (liftCells circleBaseCell3
      ⟨1, fun _ _ => 0, fun _ => continuousOn_const,
       fun _ _ _ _ hij => by omega⟩).length = 3 ∧
    (liftCells circleBaseCell4
      ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩).length = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact liftCellsAux_length _ 0 _ _ _
  · exact liftCellsAux_length _ 1 _ _ _
  · exact liftCellsAux_length _ 2 _ _ _
  · exact liftCellsAux_length _ 1 _ _ _
  · exact liftCellsAux_length _ 0 _ _ _

/-- The first-order formula $\exists x_1,\, x_1^2 + (x_0^2 + (-1)) = 0$
    representing the projection of the unit circle onto the $x_0$-axis. -/
noncomputable def circle2DFormula : orderedRing.Formula (Fin 1) :=
  BoundedFormula.ex
    ((addFunc.apply₂
      (mulFunc.apply₂
        (Term.var (Sum.inr (0 : Fin 1)) : orderedRing.Term (Fin 1 ⊕ Fin 1))
        (Term.var (Sum.inr (0 : Fin 1)) : orderedRing.Term (Fin 1 ⊕ Fin 1)))
      (addFunc.apply₂
        (mulFunc.apply₂
          (Term.var (Sum.inl (0 : Fin 1)) : orderedRing.Term (Fin 1 ⊕ Fin 1))
          (Term.var (Sum.inl (0 : Fin 1)) : orderedRing.Term (Fin 1 ⊕ Fin 1)))
        (negFunc.apply₁ (Constants.term oneFunc)))).bdEqual
      (Constants.term zeroFunc))

/-- Over $\mathbb{R}$, $\exists x_1,\, x_1^2 + (x_0^2 - 1) = 0$ holds at $v$ if
    and only if $-1 \le v(0) \le 1$. -/
theorem circle2DFormula_realize (v : Fin 1 → ℝ) :
    circle2DFormula.Realize v ↔ -1 ≤ v 0 ∧ v 0 ≤ 1 := by
  rw [Formula.Realize, circle2DFormula, BoundedFormula.realize_ex]
  constructor
  · rintro ⟨y, hy⟩
    change y * y + (v 0 * v 0 + -1) = 0 at hy
    have hsq : v 0 ^ 2 ≤ 1 := by nlinarith [mul_self_nonneg y]
    exact abs_le.mp (abs_le_one_iff_mul_self_le_one.mpr (by nlinarith))
  · rintro ⟨h1, h2⟩
    refine ⟨Real.sqrt (1 - v 0 * v 0), ?_⟩
    change Real.sqrt (1 - v 0 * v 0) * Real.sqrt (1 - v 0 * v 0) +
      (v 0 * v 0 + -1) = 0
    have hsq : Real.sqrt (1 - v 0 * v 0) * Real.sqrt (1 - v 0 * v 0) =
        1 - v 0 * v 0 :=
      Real.mul_self_sqrt (by nlinarith)
    linarith

/-- Quantifier elimination on $\exists x_1,\, x_0^2 + x_1^2 - 1 = 0$ yields a
    quantifier-free ordered-ring formula equivalent to $-1 \le v(0) \le 1$ for
    all $v : \operatorname{Fin} 1 \to \mathbb{R}$. -/
theorem circle2DFormula_qe :
    ∃ ψ : orderedRing.Formula (Fin 1),
      ψ.IsQF ∧ ∀ v : Fin 1 → ℝ, ψ.Realize v ↔ -1 ≤ v 0 ∧ v 0 ≤ 1 := by
  rcases rcf_quantifier_elimination circle2DFormula with ⟨ψ, hQF, hiff⟩
  refine ⟨ψ, hQF, fun v => (hiff v).symm.trans (circle2DFormula_realize v)⟩

end CollinsCAD
