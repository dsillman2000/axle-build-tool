import Mathlib
import CAD.EffectiveReductum
import CAD.GcdDegreeConstancy
import CAD.Derivative
import CAD.Fiber
import CAD.EffectiveFamily
import Analysis.Theorem1Mv
import Algebra.Theorem3

namespace CollinsCAD

open Polynomial MvPolynomial

/-- A continuous family of real linear polynomials with nowhere-vanishing
    leading coefficient is real-delineable by its unique root function. -/
theorem isRealDelineable_of_fiber_natDegree_eq_one
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℝ) (S : Set (Fin r → ℝ))
    (hcoeff : ∀ k : ℕ, Continuous (fun a => (fiberPoly r P a).coeff k))
    (hdeg : ∀ a ∈ S, (fiberPoly r P a).natDegree = 1)
    (hlc : ∀ a ∈ S, (fiberPoly r P a).coeff 1 ≠ 0) :
    IsRealDelineable P S := by
  classical
  let f : (Fin r → ℝ) → ℝ := fun a =>
    -((fiberPoly r P a).coeff 0) / ((fiberPoly r P a).coeff 1)
  have hlin : ∀ a ∈ S, fiberPoly r P a =
      Polynomial.C ((fiberPoly r P a).coeff 1) * Polynomial.X +
        Polynomial.C ((fiberPoly r P a).coeff 0) := by
    intro a ha
    rcases Polynomial.natDegree_eq_one.mp (hdeg a ha) with ⟨c, hc, b, h⟩
    rw [← h]
    simp
  have hfcont : ContinuousOn f S := by
    have h0 : ContinuousOn (fun a => (fiberPoly r P a).coeff 0) S :=
      (hcoeff 0).continuousOn
    have h1 : ContinuousOn (fun a => (fiberPoly r P a).coeff 1) S :=
      (hcoeff 1).continuousOn
    exact h0.neg.div h1 hlc
  have hfroot : ∀ a ∈ S, Polynomial.eval (f a) (fiberPoly r P a) = 0 := by
    intro a ha
    rw [hlin a ha]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    dsimp [f]
    field_simp [hlc a ha]
    ring
  have hfmult : ∀ a ∈ S,
      Polynomial.rootMultiplicity (f a) (fiberPoly r P a) = 1 := by
    intro a ha
    have hfactor : fiberPoly r P a =
        Polynomial.C ((fiberPoly r P a).coeff 1) *
          (Polynomial.X - Polynomial.C (f a)) := by
      rw [hlin a ha]
      dsimp [f]
      ext n
      cases n with
      | zero =>
          simp
          field_simp [hlc a ha]
      | succ n =>
          cases n with
          | zero => simp
          | succ n => simp [Polynomial.coeff_X]
    rw [hfactor, Polynomial.rootMultiplicity_mul]
    · rw [Polynomial.rootMultiplicity_C, Polynomial.rootMultiplicity_X_sub_C_self,
        zero_add]
    · exact mul_ne_zero (by simpa using hlc a ha)
        (Polynomial.monic_X_sub_C (f a)).ne_zero
  have hfexhaust : ∀ a ∈ S, ∀ x : ℝ,
      Polynomial.eval x (fiberPoly r P a) = 0 → f a = x := by
    intro a ha x hx
    rw [hlin a ha] at hx
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hx
    dsimp [f]
    symm
    rw [eq_div_iff (hlc a ha)]
    nlinarith [hx]
  refine ⟨1, fun _ => f, fun _ => 1, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hfcont
  · intro i a ha
    exact ⟨zero_lt_one, hfroot a ha, hfmult a ha⟩
  · intro a ha x hx
    exact ⟨0, hfexhaust a ha x hx⟩
  · intro i j a ha hij
    omega

/-- Collins' Theorem 4: projection sign invariance makes every polynomial
    real-delineable on a connected base set, unless its fibres vanish
    identically there. -/
theorem projection_theorem_4 {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) ℝ) (S : Set (Fin r → ℝ))
    (hS : IsConnected S) (hproj : SignInvariant (collinsProj {P}) S) :
    IsRealDelineable P S ∨ ∀ a ∈ S, fiberPoly r P a = 0 := by
  classical
  have hL : SignInvariant (projL (reductaSet {P})) S :=
    signInvariant_projL_of_collinsProj hproj
  rcases projection_effective_reductum ({P} : Finset _) P (by simp) S hL with
    hzero | ⟨k, hB0, hbridge, hBlc⟩
  · exact Or.inr hzero
  · let B : Polynomial (MvPolynomial (Fin r) ℝ) :=
      reductum k (finLastEquiv ℝ r P)
    have hBmem : B ∈ reductaSet {P} := by
      simpa [B] using reductum_mem_reductaSet (A := ({P} : Finset _))
        (P := P) (by simp) hB0
    let Q : MvPolynomial (Fin (r + 1)) ℝ := (finLastEquiv ℝ r).symm B
    have hfiberQ : ∀ a, fiberPoly r Q a = B.map (MvPolynomial.eval a) :=
      fun a => fiberPoly_finLastEquiv_symm B a
    by_cases hd0 : B.natDegree = 0
    · left
      have hdegQ : ∀ a ∈ S, (fiberPoly r Q a).natDegree = 0 := by
        intro a ha
        rw [hfiberQ, Polynomial.natDegree_map_of_leadingCoeff_ne_zero
          (MvPolynomial.eval a) (hBlc a ha), hd0]
      have hneQ : ∀ a ∈ S, fiberPoly r Q a ≠ 0 := by
        intro a ha hz
        have hc : (B.map (MvPolynomial.eval a)).coeff 0 ≠ 0 := by
          have hb : B.coeff 0 = B.leadingCoeff := by
            simp [hd0, Polynomial.leadingCoeff]
          rw [Polynomial.coeff_map, hb]
          exact hBlc a ha
        apply hc
        have hc0 := congrArg (fun q : Polynomial ℝ => q.coeff 0) hz
        rw [hfiberQ a] at hc0
        exact hc0
      have hDQ : IsRealDelineable Q S :=
        isRealDelineable_of_fiber_natDegree_eq_zero Q S hdegQ hneQ
      exact IsRealDelineable.of_fiber_eq hDQ
        (fun a ha => (hbridge a ha).trans (hfiberQ a).symm)
    · by_cases hd1 : B.natDegree = 1
      · have hdegQ1 : ∀ a ∈ S, (fiberPoly r Q a).natDegree = 1 := by
          intro a ha
          rw [hfiberQ, Polynomial.natDegree_map_of_leadingCoeff_ne_zero
            (MvPolynomial.eval a) (hBlc a ha), hd1]
        have hlcQ1 : ∀ a ∈ S, (fiberPoly r Q a).coeff 1 ≠ 0 := by
          intro a ha
          rw [hfiberQ, Polynomial.coeff_map]
          have hc : B.coeff 1 = B.leadingCoeff := by
            rw [← hd1]
            exact Polynomial.coeff_natDegree
          rw [hc]
          exact hBlc a ha
        have hcoeffQ : ∀ k : ℕ, Continuous (fun a => (fiberPoly r Q a).coeff k) := by
          intro k
          rw [show (fun a => (fiberPoly r Q a).coeff k) =
              (fun a => (B.map (MvPolynomial.eval a)).coeff k) by
            funext a
            rw [hfiberQ]]
          exact continuous_coeff_map_eval B k
        have hDQ : IsRealDelineable Q S :=
          isRealDelineable_of_fiber_natDegree_eq_one Q S hcoeffQ hdegQ1 hlcQ1
        exact Or.inl (IsRealDelineable.of_fiber_eq hDQ
          (fun a ha => (hbridge a ha).trans (hfiberQ a).symm))
      · have hdpos : 0 < B.natDegree := by omega
        let d := B.natDegree
        have hBderdeg : B.derivative.natDegree = d - 1 := by
          simp [d]
        have hBderlc : ∀ a ∈ S,
            MvPolynomial.eval a B.derivative.leadingCoeff ≠ 0 := by
          intro a ha
          exact derivative_leadingCoeff_eval_ne_zero B a hdpos (hBlc a ha)
        have hpsc : ∀ j < min d (d - 1),
            SignInvariantPoly (psc B B.derivative j) S := by
          intro j hj
          have hj' : j < B.derivative.natDegree := by
            simpa [hBderdeg, Nat.min_eq_right (Nat.sub_le _ _)] using hj
          exact hproj _ (psc_self_derivative_mem_collinsProj hBmem hj')
        obtain ⟨a₀, ha₀⟩ := hS.nonempty
        obtain ⟨gdeg, hgmin, hgcd⟩ := gcd_natDegree_constant_of_signInvariant_psc
          d (d - 1) rfl hBderdeg hBlc hBderlc hpsc ha₀
        let m := d - gdeg
        have hmapdeg : ∀ a ∈ S, (B.map (MvPolynomial.eval a)).natDegree = d := by
          intro a ha
          exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero
            (MvPolynomial.eval a) (hBlc a ha)
        have hmapne : ∀ a ∈ S, B.map (MvPolynomial.eval a) ≠ 0 := by
          intro a ha hz
          apply hBlc a ha
          have hc := congrArg (fun q : Polynomial ℝ => q.coeff d) hz
          simpa [Polynomial.coeff_map, d, Polynomial.coeff_natDegree] using hc
        have hm : ∀ a ∈ S,
            ((B.map (MvPolynomial.eval a)).map (algebraMap ℝ ℂ)).roots.toFinset.card = m := by
          intro a ha
          have hc := roots_card_distinct_eq_sub_deg_gcd_deriv
            (B.map (MvPolynomial.eval a)) (hmapne a ha)
          rw [Polynomial.derivative_map, hmapdeg a ha, hgcd a ha] at hc
          exact hc
        have hdegQ : ∀ a ∈ S, (fiberPoly r Q a).natDegree = d := by
          intro a ha
          rw [hfiberQ]
          exact hmapdeg a ha
        have hlcQ : ∀ a ∈ S, (fiberPoly r Q a).coeff d ≠ 0 := by
          intro a ha
          rw [hfiberQ, Polynomial.coeff_map]
          have hc : B.coeff d = B.leadingCoeff := by
            simp [d]
          rw [hc]
          exact hBlc a ha
        have hmQ : ∀ a ∈ S,
            ((fiberPoly r Q a).map (algebraMap ℝ ℂ)).roots.toFinset.card = m := by
          intro a ha
          rw [hfiberQ]
          exact hm a ha
        have hDQ : IsRealDelineable Q S :=
          delineability_theorem_1_real_mv Q S hS d m hdpos hdegQ hlcQ hmQ
        exact Or.inl (IsRealDelineable.of_fiber_eq hDQ
          (fun a ha => (hbridge a ha).trans (hfiberQ a).symm))

end CollinsCAD
