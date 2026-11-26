import Mathlib
import Algebra.SubresultantTheorem2

namespace CollinsCAD

open Polynomial

/-- Gauss's lemma: the degree of $\gcd(A,B)$ over a UFD is preserved after passing to its
    fraction field. -/
theorem subresultant_gauss_content_lift {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [DecidableEq R] [DecidableEq (FractionRing R)]
    [GCDMonoid (Polynomial R)] [NormalizedGCDMonoid R]
    (A B : Polynomial R) (hA0 : A ≠ 0) (hB0 : B ≠ 0) :
    (gcd A B).natDegree =
      (EuclideanDomain.gcd (A.map (algebraMap R (FractionRing R)))
        (B.map (algebraMap R (FractionRing R)))).natDegree := by
  classical
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let AR := A.map φ
  let BR := B.map φ
  let GK := EuclideanDomain.gcd AR BR
  let gR := gcd A B
  have hinj : Function.Injective φ := FaithfulSMul.algebraMap_injective R K
  have hAφ0 : AR ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hA0
  have hBφ0 : BR ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hB0
  have hGK0 : GK ≠ 0 := by
    intro hz
    have hzero := EuclideanDomain.gcd_eq_zero_iff.mp hz
    exact hAφ0 hzero.1
  have hdivgR_A : gR ∣ A := by simpa [gR] using gcd_dvd_left A B
  have hdivgR_B : gR ∣ B := by simpa [gR] using gcd_dvd_right A B
  have hgR0 : gR ≠ 0 := by
    intro hz
    rw [hz] at hdivgR_A
    exact hA0 (zero_dvd_iff.mp hdivgR_A)
  have hleft : gR.natDegree ≤ GK.natDegree := by
    have hdivA : gR.map φ ∣ AR := by
      obtain ⟨r, hr⟩ := hdivgR_A
      refine ⟨r.map φ, ?_⟩
      simpa [AR, φ, Polynomial.map_mul] using congrArg (fun p : Polynomial R => p.map φ) hr
    have hdivB : gR.map φ ∣ BR := by
      obtain ⟨r, hr⟩ := hdivgR_B
      refine ⟨r.map φ, ?_⟩
      simpa [BR, φ, Polynomial.map_mul] using congrArg (fun p : Polynomial R => p.map φ) hr
    have hdiv : gR.map φ ∣ GK := EuclideanDomain.dvd_gcd hdivA hdivB
    have hnd : (gR.map φ).natDegree ≤ GK.natDegree :=
      Polynomial.natDegree_le_of_dvd hdiv hGK0
    have hmapnd : (gR.map φ).natDegree = gR.natDegree :=
      Polynomial.natDegree_map_eq_of_injective hinj gR
    rwa [hmapnd] at hnd
  obtain ⟨b, hbM, hqmap⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors R) GK
  let q : Polynomial R := IsLocalization.integerNormalization (nonZeroDivisors R) GK
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hbM
  have hbφ : φ b ≠ 0 := by
    intro h
    exact hb0 (hinj (by simpa using h))
  have hsmul : b • GK = C (φ b) * GK := by
    simpa [φ] using (Algebra.smul_def b GK)
  have hqnd : q.natDegree = GK.natDegree := by
    have hmapnd : (q.map φ).natDegree = q.natDegree :=
      Polynomial.natDegree_map_eq_of_injective hinj q
    rw [← hmapnd]
    rw [show q.map φ = b • GK by simpa [q, φ] using hqmap, hsmul]
    exact Polynomial.natDegree_C_mul hbφ
  have hCunit : IsUnit (C (φ b) : Polynomial K) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbφ)
  have hassoc : Associated (C (φ b) * GK) GK :=
    (associated_isUnit_mul_left_iff hCunit).2 (Associated.refl GK)
  have hqdivA_K : q.map φ ∣ AR := by
    rw [show q.map φ = b • GK by simpa [q, φ] using hqmap, hsmul]
    exact (hassoc.dvd_iff_dvd_left).2 (EuclideanDomain.gcd_dvd_left AR BR)
  have hqdivB_K : q.map φ ∣ BR := by
    rw [show q.map φ = b • GK by simpa [q, φ] using hqmap, hsmul]
    exact (hassoc.dvd_iff_dvd_left).2 (EuclideanDomain.gcd_dvd_right AR BR)
  have hprim := Polynomial.isPrimitive_primPart q
  have hqprim_map_dvd : q.primPart.map φ ∣ q.map φ := by
    obtain ⟨s, hs⟩ := Polynomial.primPart_dvd q
    refine ⟨s.map φ, ?_⟩
    simpa [Polynomial.map_mul] using congrArg (fun p : Polynomial R => p.map φ) hs
  have hqprimdivA : q.primPart ∣ A := by
    apply (Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map K hprim).2
    exact (dvd_trans hqprim_map_dvd hqdivA_K)
  have hqprimdivB : q.primPart ∣ B := by
    apply (Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map K hprim).2
    exact (dvd_trans hqprim_map_dvd hqdivB_K)
  have hqprimdivg : q.primPart ∣ gR := dvd_gcd hqprimdivA hqprimdivB
  have hright : GK.natDegree ≤ gR.natDegree := by
    have hnd : q.primPart.natDegree ≤ gR.natDegree :=
      Polynomial.natDegree_le_of_dvd hqprimdivg hgR0
    rw [Polynomial.natDegree_primPart, hqnd] at hnd
    exact hnd
  exact le_antisymm hleft hright

/-- Collins' Theorem 2 over a UFD, obtained by transporting the field-valued
    statement to the fraction field. -/
theorem subresultant_deg_gcd_eq_least_nonzero_psc_ufd
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [DecidableEq R] [DecidableEq (FractionRing R)]
    [GCDMonoid (Polynomial R)] [NormalizedGCDMonoid R]
    (A B : Polynomial R) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (k : ℕ) :
    (gcd A B).natDegree = k ↔
      psc A B k ≠ 0 ∧ ∀ j < k, psc A B j = 0 := by
  classical
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let AR := A.map φ
  let BR := B.map φ
  have hinj : Function.Injective φ := FaithfulSMul.algebraMap_injective R K
  have hAφ0 : AR ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hA0
  have hBφ0 : BR ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hB0
  have hdeg : (gcd A B).natDegree = (EuclideanDomain.gcd AR BR).natDegree := by
    simpa [AR, BR, φ] using subresultant_gauss_content_lift A B hA0 hB0
  have hpsc : ∀ j, φ (psc A B j) = psc AR BR j := by
    intro j
    have hAlc : A.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hA0
    have hBlc : B.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hB0
    have hφAlc : φ A.leadingCoeff ≠ 0 := by
      intro hz
      exact hAlc (hinj (by simpa using hz))
    have hφBlc : φ B.leadingCoeff ≠ 0 := by
      intro hz
      exact hBlc (hinj (by simpa using hz))
    exact psc_map φ A B j (Or.inl hφAlc) (Or.inl hφBlc)
  constructor
  · intro hdk
    have hdkK : (EuclideanDomain.gcd AR BR).natDegree = k := by
      rw [← hdeg]
      exact hdk
    have hfield :=
      (subresultant_deg_gcd_eq_least_nonzero_psc AR BR hAφ0 hBφ0 k).mp hdkK
    refine ⟨?_, ?_⟩
    · intro hz
      apply hfield.1
      rw [← hpsc k, hz, map_zero]
    · intro j hj
      have hz := hfield.2 j hj
      rw [← hpsc j] at hz
      exact hinj (by simpa using hz)
  · rintro ⟨hpsc_k, hzeros⟩
    have hpsc_kK : psc AR BR k ≠ 0 := by
      intro hz
      apply hpsc_k
      apply hinj
      rw [hpsc k, hz, map_zero]
    have hzerosK : ∀ j < k, psc AR BR j = 0 := by
      intro j hj
      rw [← hpsc j, hzeros j hj, map_zero]
    have hfield :=
      (subresultant_deg_gcd_eq_least_nonzero_psc AR BR hAφ0 hBφ0 k).mpr
        ⟨hpsc_kK, hzerosK⟩
    rw [hdeg]
    exact hfield

end CollinsCAD
