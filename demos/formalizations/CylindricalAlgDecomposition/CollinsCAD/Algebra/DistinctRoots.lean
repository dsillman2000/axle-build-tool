import Mathlib

namespace CollinsCAD

open Polynomial
open scoped BigOperators

/-- Over $\mathbb C$, a nonzero polynomial has as many distinct roots as its degree minus the
    degree of $\gcd(P,P')$. -/
theorem card_roots_toFinset_eq_sub_gcd {P : Polynomial ℂ} (hP : P ≠ 0) :
    P.roots.toFinset.card = P.natDegree - (EuclideanDomain.gcd P P.derivative).natDegree := by
  classical
  let S := P.roots.toFinset
  let D := EuclideanDomain.gcd P P.derivative
  have hD0 : D ≠ 0 := by
    intro hD
    have hdvd := EuclideanDomain.gcd_dvd_left P P.derivative
    have hz : EuclideanDomain.gcd P P.derivative = 0 := by simpa [D] using hD
    rw [hz] at hdvd
    exact hP (zero_dvd_iff.mp hdvd)
  have hDmult : ∀ α ∈ S, Polynomial.rootMultiplicity α D = Polynomial.rootMultiplicity α P - 1 := by
    intro α hα
    have hmem : α ∈ P.roots := by simpa [S] using hα
    have hroot : P.IsRoot α := Polynomial.isRoot_of_mem_roots hmem
    have hPder : Polynomial.rootMultiplicity α P.derivative = Polynomial.rootMultiplicity α P - 1 :=
      Polynomial.derivative_rootMultiplicity_of_root hroot
    apply le_antisymm
    · have hdegpos : 0 < P.degree := Polynomial.degree_pos_of_root hP hroot
      have hPdegpos : 0 < P.natDegree := Polynomial.coe_lt_degree.mp (by simpa using hdegpos)
      have hPder0 : P.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (ne_of_gt hPdegpos)
      have hdvd := EuclideanDomain.gcd_dvd_right P P.derivative
      have hle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd
        hPder0 (by simpa [D] using hdvd) α
      rw [hPder] at hle
      exact hle
    · apply (Polynomial.le_rootMultiplicity_iff hD0).mpr
      have h1 : (X - C α) ^ (Polynomial.rootMultiplicity α P - 1) ∣ P :=
        (pow_dvd_pow (X - C α) (Nat.sub_le _ _)).trans (Polynomial.pow_rootMultiplicity_dvd P α)
      have h2 : (X - C α) ^ (Polynomial.rootMultiplicity α P - 1) ∣ P.derivative := by
        simpa [hPder] using Polynomial.pow_rootMultiplicity_dvd P.derivative α
      exact EuclideanDomain.dvd_gcd h1 h2
  have hsumP : (∑ α ∈ S, Polynomial.rootMultiplicity α P) = P.roots.card := by
    rw [← Multiset.toFinset_sum_count_eq P.roots]
    apply Finset.sum_congr rfl
    intro α hα
    rw [Polynomial.count_roots]
  have hDsum : (∑ α ∈ S, (Polynomial.rootMultiplicity α P - 1)) =
      Polynomial.natDegree D := by
    rw [← IsAlgClosed.card_roots_eq_natDegree]
    rw [← Multiset.toFinset_sum_count_eq D.roots]
    have hsubset : D.roots.toFinset ⊆ S := by
      intro α hαD
      have hmem : α ∈ D.roots := by simpa using hαD
      have hrootD : D.IsRoot α := Polynomial.isRoot_of_mem_roots hmem
      have hDP : D ∣ P := by simpa [D] using EuclideanDomain.gcd_dvd_left P P.derivative
      obtain ⟨q, hq⟩ := hDP
      have hrootP : P.IsRoot α := by
        rw [hq, Polynomial.IsRoot, Polynomial.eval_mul, hrootD, zero_mul]
      exact by simpa [S] using (Polynomial.mem_roots'.mpr ⟨hP, hrootP⟩)
    have hzero : ∀ α ∈ S, α ∉ D.roots.toFinset → Multiset.count α D.roots = 0 := by
      intro α hαS hnot
      have hnotroot : ¬ D.IsRoot α := by
        intro hr
        exact hnot (by simpa using (Polynomial.mem_roots'.mpr ⟨hD0, hr⟩))
      have hz : Polynomial.rootMultiplicity α D = 0 := Polynomial.rootMultiplicity_eq_zero hnotroot
      simp [Polynomial.count_roots, hz]
    rw [Finset.sum_subset hsubset hzero]
    apply Finset.sum_congr rfl
    intro α hα
    rw [Polynomial.count_roots, hDmult α hα]
  have hcard : S.card + Polynomial.natDegree D = P.roots.card := by
    rw [← hDsum, ← hsumP]
    calc
      S.card + (∑ α ∈ S, (Polynomial.rootMultiplicity α P - 1))
          = (∑ α ∈ S, 1) + ∑ α ∈ S, (Polynomial.rootMultiplicity α P - 1) := by simp
      _ = ∑ α ∈ S, (1 + (Polynomial.rootMultiplicity α P - 1)) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ α ∈ S, Polynomial.rootMultiplicity α P := by
            apply Finset.sum_congr rfl
            intro α hα
            have hpos : 0 < Polynomial.rootMultiplicity α P := (Polynomial.rootMultiplicity_pos hP).mpr
              (Polynomial.isRoot_of_mem_roots (by simpa [S] using hα))
            omega
  have hPcard : P.roots.card = P.natDegree := IsAlgClosed.card_roots_eq_natDegree
  rw [hPcard] at hcard
  change S.card = P.natDegree - Polynomial.natDegree D
  omega

end CollinsCAD
