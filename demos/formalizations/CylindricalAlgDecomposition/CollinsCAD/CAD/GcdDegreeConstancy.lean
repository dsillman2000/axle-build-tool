import Mathlib
import CAD.GcdDegree
import CAD.ProjectionDef
import CAD.SignInvariant
import Algebra.SubresultantTheorem2

namespace CollinsCAD

open Polynomial MvPolynomial

/-- If the PSCs below `min m n` are sign-invariant and specialization preserves
    both degrees, then the GCD degree is constant on `S`. -/
theorem gcd_natDegree_constant_of_signInvariant_psc
    {r : ℕ} {S : Set (Fin r → ℝ)}
    {U V : Polynomial (MvPolynomial (Fin r) ℝ)}
    (m n : ℕ) (hUdeg : U.natDegree = m) (hVdeg : V.natDegree = n)
    (hUlc : ∀ a ∈ S, MvPolynomial.eval a U.leadingCoeff ≠ 0)
    (hVlc : ∀ a ∈ S, MvPolynomial.eval a V.leadingCoeff ≠ 0)
    (hpsc : ∀ j < min m n, SignInvariantPoly (psc U V j) S)
    {a₀ : Fin r → ℝ} (ha₀ : a₀ ∈ S) :
    ∃ d, d ≤ min m n ∧ ∀ a ∈ S,
      (EuclideanDomain.gcd (U.map (MvPolynomial.eval a))
        (V.map (MvPolynomial.eval a))).natDegree = d := by
  classical
  have hU0 : ∀ a ∈ S, U.map (MvPolynomial.eval a) ≠ 0 := by
    intro a ha hz
    apply hUlc a ha
    have hc := congrArg (fun p : Polynomial ℝ => p.coeff U.natDegree) hz
    simpa [Polynomial.coeff_map, Polynomial.coeff_natDegree] using hc
  have hV0 : ∀ a ∈ S, V.map (MvPolynomial.eval a) ≠ 0 := by
    intro a ha hz
    apply hVlc a ha
    have hc := congrArg (fun p : Polynomial ℝ => p.coeff V.natDegree) hz
    simpa [Polynomial.coeff_map, Polynomial.coeff_natDegree] using hc
  have hUmapdeg : ∀ a ∈ S, (U.map (MvPolynomial.eval a)).natDegree = m := by
    intro a ha
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (MvPolynomial.eval a) (hUlc a ha), hUdeg]
  have hVmapdeg : ∀ a ∈ S, (V.map (MvPolynomial.eval a)).natDegree = n := by
    intro a ha
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (MvPolynomial.eval a) (hVlc a ha), hVdeg]
  have hpscmap : ∀ a ∈ S, ∀ j,
      MvPolynomial.eval a (psc U V j) =
        psc (U.map (MvPolynomial.eval a)) (V.map (MvPolynomial.eval a)) j := by
    intro a ha j
    exact psc_map (MvPolynomial.eval a) U V j
      (Or.inl (hUlc a ha)) (Or.inl (hVlc a ha))
  let U₀ := U.map (MvPolynomial.eval a₀)
  let V₀ := V.map (MvPolynomial.eval a₀)
  let d := (EuclideanDomain.gcd U₀ V₀).natDegree
  have hU00 : U₀ ≠ 0 := hU0 a₀ ha₀
  have hV00 : V₀ ≠ 0 := hV0 a₀ ha₀
  have hdU : d ≤ U₀.natDegree :=
    Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left U₀ V₀) hU00
  have hdV : d ≤ V₀.natDegree :=
    Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right U₀ V₀) hV00
  have hUdeg0 : U₀.natDegree = m := by simpa [U₀] using hUmapdeg a₀ ha₀
  have hVdeg0 : V₀.natDegree = n := by simpa [V₀] using hVmapdeg a₀ ha₀
  have hdmin : d ≤ min m n := by simpa [hUdeg0, hVdeg0] using le_min hdU hdV
  have hdpsc : psc U₀ V₀ d ≠ 0 :=
    psc_ne_zero_of_gcd_eq U₀ V₀ hU00 hV00 hdU hdV rfl
  have hdzeros : ∀ j < d, psc U₀ V₀ j = 0 := by
    intro j hj
    exact ((subresultant_deg_gcd_eq_least_nonzero_psc
      U₀ V₀ hU00 hV00 d).mp rfl).2 j hj
  have hdzeros_base : ∀ j < d, MvPolynomial.eval a₀ (psc U V j) = 0 := by
    intro j hj
    rw [hpscmap a₀ ha₀ j]
    exact hdzeros j hj
  have hzeros_all : ∀ a ∈ S, ∀ j < d,
      psc (U.map (MvPolynomial.eval a)) (V.map (MvPolynomial.eval a)) j = 0 := by
    intro a ha j hj
    rw [← hpscmap a ha j]
    exact SignInvariantPoly.eq_zero_of_eq_zero
      (hpsc j (lt_of_lt_of_le hj hdmin)) ha₀ (hdzeros_base j hj) a ha
  refine ⟨d, hdmin, ?_⟩
  by_cases hdmin_eq : d = min m n
  · intro a ha
    have hzero : ∀ j <
        min (U.map (MvPolynomial.eval a)).natDegree
            (V.map (MvPolynomial.eval a)).natDegree,
        psc (U.map (MvPolynomial.eval a)) (V.map (MvPolynomial.eval a)) j = 0 := by
      intro j hj
      apply hzeros_all a ha j
      simpa [hUmapdeg a ha, hVmapdeg a ha, hdmin_eq] using hj
    have heq := natDegree_gcd_eq_of_psc_zero_lt
      (U.map (MvPolynomial.eval a)) (V.map (MvPolynomial.eval a))
      (hU0 a ha) (hV0 a ha) hzero
    simpa [hUmapdeg a ha, hVmapdeg a ha, hdmin_eq] using heq
  · have hdlt : d < min m n := by omega
    have hdne_base : MvPolynomial.eval a₀ (psc U V d) ≠ 0 := by
      rw [hpscmap a₀ ha₀ d]
      exact hdpsc
    intro a ha
    have hne : psc (U.map (MvPolynomial.eval a))
        (V.map (MvPolynomial.eval a)) d ≠ 0 := by
      rw [← hpscmap a ha d]
      exact SignInvariantPoly.ne_zero_of_ne_zero
        (hpsc d hdlt) ha₀ hdne_base a ha
    exact (subresultant_deg_gcd_eq_least_nonzero_psc
      (U.map (MvPolynomial.eval a)) (V.map (MvPolynomial.eval a))
      (hU0 a ha) (hV0 a ha) d).mpr
        ⟨hne, fun j hj => hzeros_all a ha j hj⟩

/-- Projection-specific GCD-degree constancy for two reducta. -/
theorem gcd_natDegree_constant_of_signInvariant_collinsProj
    {r : ℕ} {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {B₁ B₂ : Polynomial (MvPolynomial (Fin r) ℝ)}
    {S : Set (Fin r → ℝ)}
    (hB₁ : B₁ ∈ reductaSet A) (hB₂ : B₂ ∈ reductaSet A)
    (hProj : SignInvariant (collinsProj A) S)
    (hB₁lc : ∀ a ∈ S, MvPolynomial.eval a B₁.leadingCoeff ≠ 0)
    (hB₂lc : ∀ a ∈ S, MvPolynomial.eval a B₂.leadingCoeff ≠ 0)
    {a₀ : Fin r → ℝ} (ha₀ : a₀ ∈ S) :
    ∃ d, d ≤ min B₁.natDegree B₂.natDegree ∧
      ∀ a ∈ S,
        (EuclideanDomain.gcd (B₁.map (MvPolynomial.eval a))
          (B₂.map (MvPolynomial.eval a))).natDegree = d := by
  refine gcd_natDegree_constant_of_signInvariant_psc
    B₁.natDegree B₂.natDegree rfl rfl hB₁lc hB₂lc ?_ ha₀
  intro j hj
  exact hProj _ (psc_mem_collinsProj hB₁ hB₂ hj)

end CollinsCAD
