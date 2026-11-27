import Mathlib
import CAD.GcdDegree
import CAD.ProjectionDef
import CAD.SignInvariant
import Algebra.SubresultantSpecialization

namespace CollinsCAD

open Polynomial MvPolynomial

/-- If source PSCs are sign-invariant, both fibres are nonzero, and at least one degree is
preserved at every point, then the GCD degree is constant.  The bound is stated at the base
point's specialized degrees, so degree drops are allowed. -/
theorem gcd_natDegree_constant_of_signInvariant_psc_of_degree_preserved
    {r : ℕ} {S : Set (Fin r → ℝ)}
    {U V : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hU0 : ∀ a ∈ S, U.map (MvPolynomial.eval a) ≠ 0)
    (hV0 : ∀ a ∈ S, V.map (MvPolynomial.eval a) ≠ 0)
    (hdeg : ∀ a ∈ S,
      (U.map (MvPolynomial.eval a)).natDegree = U.natDegree ∨
        (V.map (MvPolynomial.eval a)).natDegree = V.natDegree)
    (hpsc : ∀ j < min U.natDegree V.natDegree,
      SignInvariantPoly (psc U V j) S)
    {a₀ : Fin r → ℝ} (ha₀ : a₀ ∈ S) :
    ∃ d, d ≤ min (U.map (MvPolynomial.eval a₀)).natDegree
        (V.map (MvPolynomial.eval a₀)).natDegree ∧
      ∀ a ∈ S,
        (EuclideanDomain.gcd (U.map (MvPolynomial.eval a))
          (V.map (MvPolynomial.eval a))).natDegree = d := by
  classical
  let U₀ := U.map (MvPolynomial.eval a₀)
  let V₀ := V.map (MvPolynomial.eval a₀)
  let d := (EuclideanDomain.gcd U₀ V₀).natDegree
  have hU00 : U₀ ≠ 0 := hU0 a₀ ha₀
  have hV00 : V₀ ≠ 0 := hV0 a₀ ha₀
  have hdU : d ≤ U₀.natDegree :=
    Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left U₀ V₀) hU00
  have hdV : d ≤ V₀.natDegree :=
    Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right U₀ V₀) hV00
  have hd : d ≤ min U₀.natDegree V₀.natDegree := le_min hdU hdV
  have hmin_map (a : Fin r → ℝ) :
      min (U.map (MvPolynomial.eval a)).natDegree (V.map (MvPolynomial.eval a)).natDegree ≤
        min U.natDegree V.natDegree :=
    min_le_min Polynomial.natDegree_map_le Polynomial.natDegree_map_le
  have htransport (a : Fin r → ℝ) (ha : a ∈ S) (j : ℕ)
      (hj : j ≤ min (U.map (MvPolynomial.eval a)).natDegree
        (V.map (MvPolynomial.eval a)).natDegree) :
      MvPolynomial.eval a (psc U V j) = 0 ↔
        psc (U.map (MvPolynomial.eval a)) (V.map (MvPolynomial.eval a)) j = 0 := by
    exact psc_map_eq_zero_iff_of_natDegree_eq_left_or_right
      (MvPolynomial.eval a) U V j (hU0 a ha) (hV0 a ha) (hdeg a ha) hj
  have hdpsc : psc U₀ V₀ d ≠ 0 := psc_ne_zero_of_natDegree_gcd U₀ V₀ hU00
  have hdzeros : ∀ j < d, psc U₀ V₀ j = 0 := by
    intro j hj
    exact ((natDegree_gcd_eq_iff_psc U₀ V₀ d).mp rfl).2 j hj
  have hdzeros_base : ∀ j < d, MvPolynomial.eval a₀ (psc U V j) = 0 := by
    intro j hj
    exact (htransport a₀ ha₀ j (hj.le.trans hd)).mpr (hdzeros j hj)
  have hdne_base : MvPolynomial.eval a₀ (psc U V d) ≠ 0 := by
    intro hz
    exact hdpsc ((htransport a₀ ha₀ d hd).mp hz)
  refine ⟨d, hd, ?_⟩
  intro a ha
  let Ua := U.map (MvPolynomial.eval a)
  let Va := V.map (MvPolynomial.eval a)
  let e := (EuclideanDomain.gcd Ua Va).natDegree
  have hUa0 : Ua ≠ 0 := hU0 a ha
  have hVa0 : Va ≠ 0 := hV0 a ha
  have hemin : e ≤ min Ua.natDegree Va.natDegree :=
    le_min (Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left Ua Va) hUa0)
      (Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right Ua Va) hVa0)
  change e = d
  by_contra hne
  rcases lt_or_gt_of_ne hne with hed | hde
  · have hemin_source : e < min U.natDegree V.natDegree :=
      lt_of_lt_of_le hed (hd.trans (hmin_map a₀))
    have hpsc_e : psc Ua Va e ≠ 0 := psc_ne_zero_of_natDegree_gcd Ua Va hUa0
    have hsrc_zero : MvPolynomial.eval a (psc U V e) = 0 :=
      SignInvariantPoly.eq_zero_of_eq_zero (hpsc e hemin_source) ha₀
        (hdzeros_base e hed) a ha
    exact hpsc_e ((htransport a ha e hemin).mp hsrc_zero)
  · have hpsc_d : psc Ua Va d = 0 := psc_eq_zero_of_lt_natDegree_gcd Ua Va d hde
    have hsrc_zero : MvPolynomial.eval a (psc U V d) = 0 :=
      (htransport a ha d (hde.le.trans hemin)).mpr hpsc_d
    have hd_source : d < min U.natDegree V.natDegree :=
      lt_of_lt_of_le (lt_of_lt_of_le hde hemin) (hmin_map a)
    have hsrc_ne : MvPolynomial.eval a (psc U V d) ≠ 0 :=
      SignInvariantPoly.ne_zero_of_ne_zero (hpsc d hd_source) ha₀ hdne_base a ha
    exact hsrc_ne hsrc_zero

/-- If the PSCs below `min m n` are sign-invariant and specialization preserves both degrees,
    then the GCD degree is constant on `S`. -/
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
  have hdeg : ∀ a ∈ S,
      (U.map (MvPolynomial.eval a)).natDegree = U.natDegree ∨
        (V.map (MvPolynomial.eval a)).natDegree = V.natDegree := by
    intro a ha
    left
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (MvPolynomial.eval a) (hUlc a ha)]
  have hpsc' : ∀ j < min U.natDegree V.natDegree,
      SignInvariantPoly (psc U V j) S := by
    simpa [hUdeg, hVdeg] using hpsc
  obtain ⟨d, hd, hconst⟩ :=
    gcd_natDegree_constant_of_signInvariant_psc_of_degree_preserved
      hU0 hV0 hdeg hpsc' ha₀
  refine ⟨d, ?_, hconst⟩
  have hUdeg0 : (U.map (MvPolynomial.eval a₀)).natDegree = m := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (MvPolynomial.eval a₀) (hUlc a₀ ha₀), hUdeg]
  have hVdeg0 : (V.map (MvPolynomial.eval a₀)).natDegree = n := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (MvPolynomial.eval a₀) (hVlc a₀ ha₀), hVdeg]
  simpa [hUdeg0, hVdeg0] using hd

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

/-- Degree-drop-aware projection constancy: nonzero fibres and preservation of at least one
    degree suffice; simultaneous strict degree drops are excluded by PSC nonvanishing. -/
theorem gcd_natDegree_constant_of_signInvariant_collinsProj_of_degree_preserved
    {r : ℕ} {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {B₁ B₂ : Polynomial (MvPolynomial (Fin r) ℝ)}
    {S : Set (Fin r → ℝ)}
    (hB₁ : B₁ ∈ reductaSet A) (hB₂ : B₂ ∈ reductaSet A)
    (hProj : SignInvariant (collinsProj A) S)
    (hB₁0 : ∀ a ∈ S, B₁.map (MvPolynomial.eval a) ≠ 0)
    (hB₂0 : ∀ a ∈ S, B₂.map (MvPolynomial.eval a) ≠ 0)
    (hdeg : ∀ a ∈ S,
      (B₁.map (MvPolynomial.eval a)).natDegree = B₁.natDegree ∨
        (B₂.map (MvPolynomial.eval a)).natDegree = B₂.natDegree)
    {a₀ : Fin r → ℝ} (ha₀ : a₀ ∈ S) :
    ∃ d, d ≤ min (B₁.map (MvPolynomial.eval a₀)).natDegree
        (B₂.map (MvPolynomial.eval a₀)).natDegree ∧
      ∀ a ∈ S,
        (EuclideanDomain.gcd (B₁.map (MvPolynomial.eval a))
          (B₂.map (MvPolynomial.eval a))).natDegree = d := by
  refine gcd_natDegree_constant_of_signInvariant_psc_of_degree_preserved
    hB₁0 hB₂0 hdeg ?_ ha₀
  intro j hj
  exact hProj _ (psc_mem_collinsProj hB₁ hB₂ hj)

end CollinsCAD
