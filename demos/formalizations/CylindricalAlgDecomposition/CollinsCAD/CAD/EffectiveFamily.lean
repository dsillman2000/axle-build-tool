import Mathlib
import CAD.GcdDegreeConstancy
import CAD.Derivative
import Algebra.Theorem3

namespace CollinsCAD

open Polynomial MvPolynomial

/-- Coefficients of the specialization of a fixed univariate coefficient
    polynomial vary continuously. -/
theorem continuous_coeff_map_eval {r : ℕ}
    (B : Polynomial (MvPolynomial (Fin r) ℝ)) (k : ℕ) :
    Continuous (fun a : Fin r → ℝ => (B.map (MvPolynomial.eval a)).coeff k) := by
  have hfun : (fun a : Fin r → ℝ => (B.map (MvPolynomial.eval a)).coeff k) =
      (fun a : Fin r → ℝ => MvPolynomial.eval a (B.coeff k)) := by
    funext a
    rw [Polynomial.coeff_map]
  rw [hfun]
  exact (MvPolynomial.continuous_eval _).comp continuous_id

/-- Positive-degree effective reducta have constant degree and constant number
    of distinct complex roots on a projection-invariant base set. -/
theorem projection_reductum_family_data_of_natDegree_pos
    {r : ℕ} {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {B : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hB : B ∈ reductaSet A) (S : Set (Fin r → ℝ))
    (hproj : SignInvariant (collinsProj A) S)
    (hBlc : ∀ a ∈ S, MvPolynomial.eval a B.leadingCoeff ≠ 0)
    {a₀ : Fin r → ℝ} (ha₀ : a₀ ∈ S) (hdpos : 0 < B.natDegree) :
    ∃ d m, B.natDegree = d ∧ 0 < d ∧
      (∀ a ∈ S, (B.map (MvPolynomial.eval a)).natDegree = d) ∧
      (∀ a ∈ S,
        ((B.map (MvPolynomial.eval a)).map (algebraMap ℝ ℂ)).roots.toFinset.card = m) := by
  classical
  let d := B.natDegree
  have hBderdeg : B.derivative.natDegree = d - 1 := by simp [d]
  have hBderlc : ∀ a ∈ S, MvPolynomial.eval a B.derivative.leadingCoeff ≠ 0 := by
    intro a ha
    exact derivative_leadingCoeff_eval_ne_zero B a hdpos (hBlc a ha)
  have hpsc : ∀ j < min d (d - 1), SignInvariantPoly (psc B B.derivative j) S := by
    intro j hj
    have hj' : j < B.derivative.natDegree := by
      simpa [hBderdeg, Nat.min_eq_right (Nat.sub_le _ _)] using hj
    exact hproj _ (psc_self_derivative_mem_collinsProj hB hj')
  obtain ⟨gdeg, hgmin, hgcd⟩ :=
    gcd_natDegree_constant_of_signInvariant_psc d (d - 1) rfl hBderdeg
      hBlc hBderlc hpsc ha₀
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
  exact ⟨d, m, rfl, hdpos, hmapdeg, hm⟩

end CollinsCAD
