import Mathlib
import Algebra.GcdDegreeZero

namespace CollinsCAD

open Polynomial

/-- Collins' Theorem 2: $\deg\gcd(A,B)=k$ precisely when $\operatorname{psc}_k(A,B)\neq0$ and
    all earlier principal subresultant coefficients vanish. -/
theorem subresultant_deg_gcd_eq_least_nonzero_psc {K : Type*} [Field K] [DecidableEq K]
    (A B : Polynomial K) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (k : ℕ) :
    (EuclideanDomain.gcd A B).natDegree = k ↔
      psc A B k ≠ 0 ∧ ∀ j < k, psc A B j = 0 := by
  classical
  let d := (EuclideanDomain.gcd A B).natDegree
  have hdA : d ≤ A.natDegree :=
    Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left A B) hA0
  have hdB : d ≤ B.natDegree :=
    Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right A B) hB0
  constructor
  · intro hdk
    refine ⟨?_, ?_⟩
    · have hj : d = k := by simpa [d] using hdk
      simpa [d, hj] using (psc_ne_zero_of_gcd_eq A B hA0 hB0 hdA hdB hj)
    · intro j hj
      have hjd : j < d := by simpa [d, hdk] using hj
      have hjA : j < A.natDegree := lt_of_lt_of_le hjd hdA
      have hjB : j < B.natDegree := lt_of_lt_of_le hjd hdB
      exact psc_eq_zero_of_lt_gcd A B hA0 hB0 j hjA hjB hjd
  · rintro ⟨hpsc_k, hzeros⟩
    by_contra hne
    have hlt_or_gt : d < k ∨ k < d := by omega
    rcases hlt_or_gt with hdk | hkd
    · have hpsc_d0 : psc A B d = 0 := hzeros d hdk
      have hpsc_dne : psc A B d ≠ 0 := by
        have hd_eq : d = d := rfl
        simpa [d] using (psc_ne_zero_of_gcd_eq A B hA0 hB0 hdA hdB hd_eq)
      exact hpsc_dne hpsc_d0
    · have hkA : k < A.natDegree := lt_of_lt_of_le hkd hdA
      have hkB : k < B.natDegree := lt_of_lt_of_le hkd hdB
      exact hpsc_k (psc_eq_zero_of_lt_gcd A B hA0 hB0 k hkA hkB hkd)

end CollinsCAD
