import Mathlib
import Analysis.Delineability

namespace CollinsCAD

open Polynomial MvPolynomial
open scoped BigOperators

variable {r : ℕ}

/-- Fibres of the multivariate polynomial corresponding to a univariate
    coefficient polynomial are its specializations. -/
theorem fiberPoly_finLastEquiv_symm (B : Polynomial (MvPolynomial (Fin r) ℝ))
    (a : Fin r → ℝ) :
    fiberPoly r ((finLastEquiv ℝ r).symm B) a = B.map (MvPolynomial.eval a) := by
  simp [fiberPoly]

/-- Real delineability depends only on the fibres on the base set. -/
theorem IsRealDelineable.of_fiber_eq
    {P Q : MvPolynomial (Fin (r + 1)) ℝ} {S : Set (Fin r → ℝ)}
    (hD : IsRealDelineable Q S)
    (h : ∀ a ∈ S, fiberPoly r P a = fiberPoly r Q a) :
    IsRealDelineable P S := by
  rcases hD with ⟨k, f, e, hcont, hroot, hexhaust, hmono⟩
  refine ⟨k, f, e, hcont, ?_, ?_, hmono⟩
  · intro i a ha
    simpa [h a ha] using hroot i a ha
  · intro a ha x hx
    apply hexhaust a ha x
    simpa [h a ha] using hx

/-- A real-delineable polynomial has no identically zero fibre. -/
theorem fiberPoly_ne_zero_of_isRealDelineable
    {P : MvPolynomial (Fin (r + 1)) ℝ} {S : Set (Fin r → ℝ)}
    (hD : IsRealDelineable P S) (a : Fin r → ℝ) (ha : a ∈ S) :
    fiberPoly r P a ≠ 0 := by
  rcases hD with ⟨k, f, e, hcont, hroot, hexhaust, hmono⟩
  intro hz
  have huniv : Set.range (fun i : Fin k => f i a) = (Set.univ : Set ℝ) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_univ x
    · intro hx
      have hxroot : Polynomial.eval x (fiberPoly r P a) = 0 := by simp [hz]
      rcases hexhaust a ha x hxroot with ⟨i, hi⟩
      exact ⟨i, hi⟩
  have hfin : (Set.univ : Set ℝ).Finite := by
    rw [← huniv]
    exact Set.finite_range (fun i : Fin k => f i a)
  exact Set.infinite_univ.not_finite hfin

/-- Fibres commute with finite products. -/
theorem fiberPoly_prod (A : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (a : Fin r → ℝ) :
    fiberPoly r (∏ P ∈ A, P) a = ∏ P ∈ A, fiberPoly r P a := by
  change Polynomial.map (MvPolynomial.eval a)
    (((finLastEquiv ℝ r).toAlgHom) (∏ P ∈ A, P)) = _
  rw [map_prod]
  simp only [fiberPoly]
  rw [Polynomial.map_prod]
  rfl

/-- A point is a root of a product fibre exactly when it is a root of one of
    the factor fibres. -/
theorem fiberPoly_eval_prod_eq_zero_iff
    (A : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (a : Fin r → ℝ) (x : ℝ) :
    Polynomial.eval x (fiberPoly r (∏ P ∈ A, P) a) = 0 ↔
      ∃ P ∈ A, Polynomial.eval x (fiberPoly r P a) = 0 := by
  rw [fiberPoly_prod]
  change (Polynomial.evalRingHom x) (∏ P ∈ A, fiberPoly r P a) = 0 ↔ _
  rw [map_prod, Finset.prod_eq_zero_iff]
  rfl

/-- Root multiplicity is additive over a finite product of nonzero fibres. -/
theorem rootMultiplicity_fiberPoly_prod
    (A : Finset (MvPolynomial (Fin (r + 1)) ℝ)) (a : Fin r → ℝ)
    (hne : ∀ P ∈ A, fiberPoly r P a ≠ 0) (x : ℝ) :
    Polynomial.rootMultiplicity x (fiberPoly r (∏ P ∈ A, P) a) =
      ∑ P ∈ A, Polynomial.rootMultiplicity x (fiberPoly r P a) := by
  classical
  rw [fiberPoly_prod]
  have hgen : ∀ B : Finset (MvPolynomial (Fin (r + 1)) ℝ),
      (∀ P ∈ B, fiberPoly r P a ≠ 0) →
      Polynomial.rootMultiplicity x (∏ P ∈ B, fiberPoly r P a) =
        ∑ P ∈ B, Polynomial.rootMultiplicity x (fiberPoly r P a) := by
    intro B
    induction B using Finset.induction_on with
    | empty => simp
    | @insert P B hP ih =>
      intro hneB
      have hPne := hneB P (Finset.mem_insert_self P B)
      have hBne : ∀ Q ∈ B, fiberPoly r Q a ≠ 0 :=
        fun Q hQ => hneB Q (Finset.mem_insert_of_mem hQ)
      have hprod : (∏ Q ∈ B, fiberPoly r Q a) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr hBne
      rw [Finset.prod_insert hP, Finset.sum_insert hP,
        Polynomial.rootMultiplicity_mul (mul_ne_zero hPne hprod), ih hBne]
  exact hgen A hne

end CollinsCAD
