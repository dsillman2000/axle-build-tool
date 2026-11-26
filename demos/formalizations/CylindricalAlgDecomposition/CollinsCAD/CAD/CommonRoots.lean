import Mathlib

namespace CollinsCAD

open Polynomial
open scoped BigOperators

/-- Root multiplicity in a GCD is the minimum of the multiplicities in the two
    nonzero polynomials. -/
theorem rootMultiplicity_gcd {K : Type*} [Field K] [DecidableEq K]
    (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) (z : K) :
    Polynomial.rootMultiplicity z (EuclideanDomain.gcd p q) =
      min (Polynomial.rootMultiplicity z p) (Polynomial.rootMultiplicity z q) := by
  have hgcd0 : EuclideanDomain.gcd p q ≠ 0 := by
    intro hz
    have hdvd := EuclideanDomain.gcd_dvd_left p q
    rw [hz] at hdvd
    exact hp (zero_dvd_iff.mp hdvd)
  apply le_antisymm
  · exact le_min
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hp
        (EuclideanDomain.gcd_dvd_left p q) z)
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hq
        (EuclideanDomain.gcd_dvd_right p q) z)
  · apply (Polynomial.le_rootMultiplicity_iff hgcd0).mpr
    have h1 : (Polynomial.X - Polynomial.C z) ^
        min (Polynomial.rootMultiplicity z p) (Polynomial.rootMultiplicity z q) ∣ p :=
      (pow_dvd_pow (Polynomial.X - Polynomial.C z) (min_le_left _ _)).trans
        (Polynomial.pow_rootMultiplicity_dvd p z)
    have h2 : (Polynomial.X - Polynomial.C z) ^
        min (Polynomial.rootMultiplicity z p) (Polynomial.rootMultiplicity z q) ∣ q :=
      (pow_dvd_pow (Polynomial.X - Polynomial.C z) (min_le_right _ _)).trans
        (Polynomial.pow_rootMultiplicity_dvd q z)
    exact EuclideanDomain.dvd_gcd h1 h2

/-- Over an algebraically closed field, the degree of a GCD is the sum of the
    minimum root multiplicities over the roots of the first polynomial. -/
theorem natDegree_gcd_eq_sum_min_rootMultiplicity
    (p q : Polynomial ℂ) (hp : p ≠ 0) (hq : q ≠ 0) :
    (EuclideanDomain.gcd p q).natDegree =
      ∑ z ∈ p.roots.toFinset,
        min (Polynomial.rootMultiplicity z p) (Polynomial.rootMultiplicity z q) := by
  have hgcd0 : EuclideanDomain.gcd p q ≠ 0 := by
    intro hz
    have hdvd := EuclideanDomain.gcd_dvd_left p q
    rw [hz] at hdvd
    exact hp (zero_dvd_iff.mp hdvd)
  rw [← IsAlgClosed.card_roots_eq_natDegree]
  rw [← Multiset.toFinset_sum_count_eq (EuclideanDomain.gcd p q).roots]
  have hsubset : (EuclideanDomain.gcd p q).roots.toFinset ⊆ p.roots.toFinset := by
    intro z hz
    have hmem : z ∈ (EuclideanDomain.gcd p q).roots := Multiset.mem_toFinset.mp hz
    have hroot : (EuclideanDomain.gcd p q).IsRoot z := Polynomial.isRoot_of_mem_roots hmem
    have hdvd : EuclideanDomain.gcd p q ∣ p := EuclideanDomain.gcd_dvd_left p q
    obtain ⟨w, hw⟩ := hdvd
    have hrootp : p.IsRoot z := by
      rw [hw, Polynomial.IsRoot, Polynomial.eval_mul, hroot, zero_mul]
    exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hp, hrootp⟩)
  have hzero : ∀ z ∈ p.roots.toFinset,
      z ∉ (EuclideanDomain.gcd p q).roots.toFinset →
        Multiset.count z (EuclideanDomain.gcd p q).roots = 0 := by
    intro z hz hnot
    have hnotroot : ¬ (EuclideanDomain.gcd p q).IsRoot z := by
      intro hr
      exact hnot (Multiset.mem_toFinset.mpr
        (Polynomial.mem_roots'.mpr ⟨hgcd0, hr⟩))
    have hz0 : Polynomial.rootMultiplicity z (EuclideanDomain.gcd p q) = 0 :=
      Polynomial.rootMultiplicity_eq_zero hnotroot
    simp [Polynomial.count_roots, hz0]
  rw [Finset.sum_subset hsubset hzero]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Polynomial.count_roots, rootMultiplicity_gcd p q hp hq z]

/-- The natural degree of a polynomial GCD. -/
noncomputable def gcdNatDegree {K : Type*} [Field K] [DecidableEq K]
    (A B : Polynomial K) : ℕ :=
  (EuclideanDomain.gcd A B).natDegree

/-- The finite set of common complex roots. -/
noncomputable def commonRootFinset (A B : Polynomial ℂ) : Finset ℂ :=
  A.roots.toFinset ∩ B.roots.toFinset

/-- The roots of a nonzero GCD are exactly the common roots. -/
theorem gcd_roots_toFinset_eq_inter {A B : Polynomial ℂ}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    (EuclideanDomain.gcd A B).roots.toFinset = commonRootFinset A B := by
  classical
  have hG : EuclideanDomain.gcd A B ≠ 0 := by
    intro hz
    have hdvd := EuclideanDomain.gcd_dvd_left A B
    rw [hz] at hdvd
    exact hA (zero_dvd_iff.mp hdvd)
  ext z
  simp only [commonRootFinset, Finset.mem_inter, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hG, Polynomial.mem_roots hA, Polynomial.mem_roots hB,
    Polynomial.isRoot_gcd_iff_isRoot_left_right]

/-- Degree over an algebraically closed field is the sum of root
    multiplicities. -/
theorem natDegree_eq_sum_rootMultiplicity (G : Polynomial ℂ) :
    G.natDegree = ∑ z ∈ G.roots.toFinset, Polynomial.rootMultiplicity z G := by
  rw [← IsAlgClosed.card_roots_eq_natDegree (p := G)]
  rw [← Multiset.toFinset_sum_count_eq G.roots]
  apply Finset.sum_congr rfl
  intro z hz
  simp

/-- GCD degree over an algebraically closed field is the sum of minimum root
    multiplicities over common roots. -/
theorem gcdNatDegree_eq_sum_min {A B : Polynomial ℂ}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    gcdNatDegree A B = ∑ z ∈ commonRootFinset A B,
      min (Polynomial.rootMultiplicity z A) (Polynomial.rootMultiplicity z B) := by
  let G := EuclideanDomain.gcd A B
  have hG : G ≠ 0 := by
    intro hz
    dsimp [G] at hz
    have hdvd := EuclideanDomain.gcd_dvd_left A B
    rw [hz] at hdvd
    exact hA (zero_dvd_iff.mp hdvd)
  calc
    gcdNatDegree A B = ∑ z ∈ G.roots.toFinset, Polynomial.rootMultiplicity z G := by
      simpa [gcdNatDegree, G] using natDegree_eq_sum_rootMultiplicity G
    _ = ∑ z ∈ G.roots.toFinset,
        min (Polynomial.rootMultiplicity z A) (Polynomial.rootMultiplicity z B) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact rootMultiplicity_gcd A B hA hB z
    _ = ∑ z ∈ commonRootFinset A B,
        min (Polynomial.rootMultiplicity z A) (Polynomial.rootMultiplicity z B) := by
      rw [gcd_roots_toFinset_eq_inter hA hB]

/-- Mapping real polynomials to the complex numbers preserves GCD degree. -/
theorem gcdNatDegree_map_real_to_complex (A B : Polynomial ℝ) :
    gcdNatDegree (A.map (algebraMap ℝ ℂ)) (B.map (algebraMap ℝ ℂ)) =
      gcdNatDegree A B := by
  have h : EuclideanDomain.gcd (A.map (algebraMap ℝ ℂ)) (B.map (algebraMap ℝ ℂ)) =
      (EuclideanDomain.gcd A B).map (algebraMap ℝ ℂ) := by
    simpa using (Polynomial.gcd_map (p := A) (q := B) (algebraMap ℝ ℂ))
  rw [gcdNatDegree, gcdNatDegree, h]
  exact Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective _

/-- Multiplying the second polynomial by a nonzero constant does not change
    GCD degree. -/
theorem gcdNatDegree_mul_C_right (A B : Polynomial ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    gcdNatDegree A (B * Polynomial.C c) = gcdNatDegree A B := by
  have hB' : B * Polynomial.C c ≠ 0 := mul_ne_zero hB (by simpa using hc)
  have hroots : (B * Polynomial.C c).roots.toFinset = B.roots.toFinset := by
    rw [mul_comm, Polynomial.roots_C_mul _ hc]
  have hcommon : commonRootFinset A (B * Polynomial.C c) = commonRootFinset A B := by
    ext z
    simp [commonRootFinset, hroots]
  rw [gcdNatDegree_eq_sum_min hA hB', gcdNatDegree_eq_sum_min hA hB, hcommon]
  apply Finset.sum_congr rfl
  intro z hz
  have hmult : Polynomial.rootMultiplicity z (B * Polynomial.C c) =
      Polynomial.rootMultiplicity z B := by
    rw [mul_comm, Polynomial.rootMultiplicity_mul]
    · simp [Polynomial.rootMultiplicity_C]
    · exact mul_ne_zero (by simpa using hc) hB
  simp [hmult]

/-- GCD degree is symmetric. -/
theorem gcdNatDegree_comm {A B : Polynomial ℂ} (hA : A ≠ 0) (hB : B ≠ 0) :
    gcdNatDegree A B = gcdNatDegree B A := by
  have hcomm : commonRootFinset A B = commonRootFinset B A := by
    ext w
    simp [commonRootFinset, Finset.inter_comm]
  rw [gcdNatDegree_eq_sum_min hA hB, gcdNatDegree_eq_sum_min hB hA, hcomm]
  apply Finset.sum_congr rfl
  intro z hz
  simp [min_comm]

/-- Multiplying the first polynomial by a nonzero constant does not change
    GCD degree. -/
theorem gcdNatDegree_mul_C_left (A B : Polynomial ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    gcdNatDegree (A * Polynomial.C c) B = gcdNatDegree A B := by
  have hA' : A * Polynomial.C c ≠ 0 := mul_ne_zero hA (by simpa using hc)
  rw [gcdNatDegree_comm hA' hB, gcdNatDegree_mul_C_right B A hB hA c hc,
    gcdNatDegree_comm hB hA]

end CollinsCAD
