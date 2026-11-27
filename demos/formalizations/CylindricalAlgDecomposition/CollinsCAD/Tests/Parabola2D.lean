import Mathlib
import Tests.Linear1D

/-!
# Trivial CAD test 2: two-dimensional parabola $x_1^2 + x_0$

This file pins down the explicit CAD projection, subresultant discriminant,
fibre root structure, and first-order quantifier elimination for the parabola
$P(x_0, x_1) = x_1^2 + x_0 \in \mathbb{R}[x_0, x_1]$.
-/

open scoped FirstOrder.Language

namespace CollinsCAD

open Polynomial MvPolynomial FirstOrder FirstOrder.Language

/-- The two-dimensional parabola polynomial $P(x_0, x_1) = x_1^2 + x_0$. -/
noncomputable def parabola2DPoly : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.X 1 ^ 2 + MvPolynomial.X 0

/-- Under `finLastEquiv`, $x_1^2 + x_0$ becomes
    $X^2 + C(x_0) \in \mathbb{R}[x_0][X]$. -/
theorem finLastEquiv_parabola2DPoly :
    finLastEquiv ℝ 1 parabola2DPoly =
      Polynomial.X ^ 2 + Polynomial.C (MvPolynomial.X 0) := by
  change finLastEquiv ℝ 1
      (MvPolynomial.X (Fin.last 1) ^ 2 + MvPolynomial.X (Fin.castSucc 0)) =
    Polynomial.X ^ 2 + Polynomial.C (MvPolynomial.X 0)
  rw [map_add, map_pow, finLastEquiv_X_last, finLastEquiv_X_castSucc]

/-- The fibre polynomial of $x_1^2 + x_0$ over $a = (a_0) \in \mathbb{R}^1$ is
    $X^2 + C(a_0) \in \mathbb{R}[X]$. -/
theorem fiberPoly_parabola2DPoly (a : Fin 1 → ℝ) :
    fiberPoly 1 parabola2DPoly a = Polynomial.X ^ 2 + Polynomial.C (a 0) := by
  simp [fiberPoly, finLastEquiv_parabola2DPoly]

/-- The zeroth reductum of $X^2 + C(x_0)$ is $X^2 + C(x_0)$. -/
theorem reductum_zero_parabola2DPoly :
    reductum 0 (finLastEquiv ℝ 1 parabola2DPoly) =
      Polynomial.X ^ 2 + Polynomial.C (MvPolynomial.X 0) := by
  rw [reductum_zero, finLastEquiv_parabola2DPoly]

/-- The degree of $X^2 + C(x_0)$ in the last variable is $2$. -/
theorem natDegree_parabola2DLast :
    (Polynomial.X ^ 2 +
      Polynomial.C (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)).natDegree = 2 := by
  simp

/-- The leading coefficient of $X^2 + C(x_0)$ in the last variable is $1$. -/
theorem leadingCoeff_parabola2DLast :
    (Polynomial.X ^ 2 +
      Polynomial.C (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, natDegree_parabola2DLast]
  simp

/-- The first reductum of $X^2 + C(x_0)$ is the constant polynomial $C(x_0)$. -/
theorem reductum_one_parabola2DPoly :
    reductum 1 (finLastEquiv ℝ 1 parabola2DPoly) =
      Polynomial.C (MvPolynomial.X 0) := by
  rw [reductum_succ, reductum_zero_parabola2DPoly, eraseLead_eq_sub_leadingTerm,
    natDegree_parabola2DLast, leadingCoeff_parabola2DLast]
  simp

/-- The second reductum of $X^2 + C(x_0)$ vanishes. -/
theorem reductum_two_parabola2DPoly :
    reductum 2 (finLastEquiv ℝ 1 parabola2DPoly) = 0 := by
  rw [reductum_succ, reductum_one_parabola2DPoly, Polynomial.eraseLead_C]

/-- Both $1$ and $x_0$ belong to the leading-coefficient projection `projL`
    (and hence `collinsProj`) of $\{x_1^2 + x_0\}$. -/
theorem leadingCoeffs_mem_collinsProj_parabola2DPoly :
    (1 : MvPolynomial (Fin 1) ℝ) ∈ collinsProj {parabola2DPoly} ∧
    (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) ∈ collinsProj {parabola2DPoly} := by
  refine ⟨?_, ?_⟩
  · have hne0 : reductum 0 (finLastEquiv ℝ 1 parabola2DPoly) ≠ 0 := by
      intro h0
      have hlc := congrArg Polynomial.leadingCoeff h0
      rw [reductum_zero_parabola2DPoly, leadingCoeff_parabola2DLast,
        Polynomial.leadingCoeff_zero] at hlc
      exact one_ne_zero hlc
    have hmem0 := reductum_mem_reductaSet (A := {parabola2DPoly}) (by simp) hne0
    have hlc0 : (reductum 0 (finLastEquiv ℝ 1 parabola2DPoly)).leadingCoeff = 1 := by
      rw [reductum_zero_parabola2DPoly, leadingCoeff_parabola2DLast]
    rw [← hlc0]
    exact leadingCoeff_mem_collinsProj hmem0
  · have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) ≠ 0 :=
      MvPolynomial.X_ne_zero 0
    have hne1 : reductum 1 (finLastEquiv ℝ 1 parabola2DPoly) ≠ 0 := by
      rw [reductum_one_parabola2DPoly]
      exact Polynomial.C_ne_zero.mpr hX0
    have hmem1 := reductum_mem_reductaSet (A := {parabola2DPoly}) (by simp) hne1
    have hlc1 : (reductum 1 (finLastEquiv ℝ 1 parabola2DPoly)).leadingCoeff =
        MvPolynomial.X 0 := by
      rw [reductum_one_parabola2DPoly, Polynomial.leadingCoeff_C]
    rw [← hlc1]
    exact leadingCoeff_mem_collinsProj hmem1

/-- The formal derivative of $X^2 + C(c)$ is $C(2)\,X$. -/
theorem derivative_X_sq_add_C {R : Type*} [CommRing R] (c : R) :
    (Polynomial.X ^ 2 + Polynomial.C c).derivative =
      Polynomial.C 2 * Polynomial.X := by
  simp [map_ofNat]
  ring

/-- The fixed-bound $0$-th principal subresultant (resultant) of $X^2 + C(c)$
    and its derivative $C(2)\,X$ at degree bounds $(2, 1)$ is $4c$. -/
theorem fixed_psc_X_sq_add_C_derivative {R : Type*} [CommRing R] (c : R) :
    Polynomial.psc (Polynomial.X ^ 2 + Polynomial.C c)
      (Polynomial.C 2 * Polynomial.X) 2 1 0 = 4 * c := by
  rw [Polynomial.psc_def]
  let M := Polynomial.subresultantMatrix
    (Polynomial.X ^ 2 + Polynomial.C c) (Polynomial.C 2 * Polynomial.X) 2 1 0
  change M.det = 4 * c
  have h00 : M 0 0 = 0 := by
    change M 0 (Fin.castAdd 1 (0 : Fin 2)) = 0
    dsimp only [M]
    rw [Polynomial.subresultantMatrix_castAdd]
    simp
  have h01 : M 0 1 = 0 := by
    change M 0 (Fin.castAdd 1 (1 : Fin 2)) = 0
    dsimp only [M]
    rw [Polynomial.subresultantMatrix_castAdd]
    simp
  have h02 : M 0 2 = c := by
    change M 0 (Fin.natAdd 2 (0 : Fin 1)) = c
    dsimp only [M]
    rw [Polynomial.subresultantMatrix_natAdd]
    simp
  have h10 : M 1 0 = 2 := by
    change M 1 (Fin.castAdd 1 (0 : Fin 2)) = 2
    dsimp only [M]
    rw [Polynomial.subresultantMatrix_castAdd]
    simp
  have h11 : M 1 1 = 0 := by
    change M 1 (Fin.castAdd 1 (1 : Fin 2)) = 0
    dsimp only [M]
    rw [Polynomial.subresultantMatrix_castAdd]
    simp
  have h12 : M 1 2 = 0 := by
    change M 1 (Fin.natAdd 2 (0 : Fin 1)) = 0
    dsimp only [M]
    rw [Polynomial.subresultantMatrix_natAdd]
    simp
  have h20 : M 2 0 = 0 := by
    change M 2 (Fin.castAdd 1 (0 : Fin 2)) = 0
    dsimp only [M]
    rw [Polynomial.subresultantMatrix_castAdd]
    simp
  have h21 : M 2 1 = 2 := by
    change M 2 (Fin.castAdd 1 (1 : Fin 2)) = 2
    dsimp only [M]
    rw [Polynomial.subresultantMatrix_castAdd]
    simp
  have h22 : M 2 2 = 1 := by
    change M 2 (Fin.natAdd 2 (0 : Fin 1)) = 1
    dsimp only [M]
    rw [Polynomial.subresultantMatrix_natAdd]
    simp
  rw [Matrix.det_fin_three, h00, h01, h02, h10, h11, h12, h20, h21, h22]
  ring

/-- The actual-degree $0$-th principal subresultant of $X^2 + C(x_0)$ with its
    derivative is $4 x_0$, and $4 x_0$ belongs to `collinsProj {x_1^2 + x_0}`. -/
theorem discriminant_mem_collinsProj_parabola2DPoly :
    psc (finLastEquiv ℝ 1 parabola2DPoly)
      (finLastEquiv ℝ 1 parabola2DPoly).derivative 0 =
        4 * MvPolynomial.X 0 ∧
    (4 * MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) ∈
      collinsProj {parabola2DPoly} := by
  have hderiv : (finLastEquiv ℝ 1 parabola2DPoly).derivative =
      Polynomial.C 2 * Polynomial.X := by
    rw [finLastEquiv_parabola2DPoly, derivative_X_sq_add_C]
  have hdegP : (finLastEquiv ℝ 1 parabola2DPoly).natDegree = 2 := by
    rw [finLastEquiv_parabola2DPoly, natDegree_parabola2DLast]
  have hdegD : (finLastEquiv ℝ 1 parabola2DPoly).derivative.natDegree = 1 := by
    rw [hderiv, Polynomial.natDegree_C_mul_X]
    norm_num
  have hpsc : psc (finLastEquiv ℝ 1 parabola2DPoly)
      (finLastEquiv ℝ 1 parabola2DPoly).derivative 0 =
        4 * MvPolynomial.X 0 := by
    rw [psc_eq_fixed_psc, hdegP, hdegD, finLastEquiv_parabola2DPoly,
      derivative_X_sq_add_C, fixed_psc_X_sq_add_C_derivative]
    ring
  refine ⟨hpsc, ?_⟩
  have hne0 : reductum 0 (finLastEquiv ℝ 1 parabola2DPoly) ≠ 0 := by
    rw [reductum_zero]
    intro h0
    rw [h0] at hdegP
    simp at hdegP
  have hmem0 := reductum_mem_reductaSet (A := {parabola2DPoly}) (by simp) hne0
  rw [reductum_zero] at hmem0
  rw [← hpsc]
  exact psc_self_derivative_mem_collinsProj hmem0 (by omega)

/-- The first-order formula $\exists x_1,\, x_1^2 + x_0 = 0$ in one free variable
    $x_0$. -/
noncomputable def parabola2DFormula : orderedRing.Formula (Fin 1) :=
  BoundedFormula.ex
    ((addFunc.apply₂
      (mulFunc.apply₂
        (Term.var (Sum.inr (0 : Fin 1)) : orderedRing.Term (Fin 1 ⊕ Fin 1))
        (Term.var (Sum.inr (0 : Fin 1)) : orderedRing.Term (Fin 1 ⊕ Fin 1)))
      (Term.var (Sum.inl (0 : Fin 1)) : orderedRing.Term (Fin 1 ⊕ Fin 1))).bdEqual
      (Constants.term zeroFunc))

/-- Over $\mathbb{R}$, $\exists x_1,\, x_1^2 + x_0 = 0$ holds at $v$ if and only
    if $v(0) \le 0$. -/
theorem parabola2DFormula_realize (v : Fin 1 → ℝ) :
    parabola2DFormula.Realize v ↔ v 0 ≤ 0 := by
  rw [Formula.Realize, parabola2DFormula, BoundedFormula.realize_ex]
  constructor
  · rintro ⟨y, hy⟩
    change y * y + v 0 = 0 at hy
    nlinarith [mul_self_nonneg y]
  · intro hv
    refine ⟨Real.sqrt (-v 0), ?_⟩
    change Real.sqrt (-v 0) * Real.sqrt (-v 0) + v 0 = 0
    have hsq : Real.sqrt (-v 0) * Real.sqrt (-v 0) = -v 0 :=
      Real.mul_self_sqrt (by linarith)
    linarith

/-- Quantifier elimination on $\exists x_1,\, x_1^2 + x_0 = 0$ yields a
    quantifier-free ordered-ring formula equivalent to $v(0) \le 0$ for all
    $v : \operatorname{Fin} 1 \to \mathbb{R}$. -/
theorem parabola2DFormula_qe :
    ∃ ψ : orderedRing.Formula (Fin 1),
      ψ.IsQF ∧ ∀ v : Fin 1 → ℝ, ψ.Realize v ↔ v 0 ≤ 0 := by
  rcases rcf_quantifier_elimination parabola2DFormula with ⟨ψ, hQF, hiff⟩
  refine ⟨ψ, hQF, fun v => (hiff v).symm.trans (parabola2DFormula_realize v)⟩

end CollinsCAD
