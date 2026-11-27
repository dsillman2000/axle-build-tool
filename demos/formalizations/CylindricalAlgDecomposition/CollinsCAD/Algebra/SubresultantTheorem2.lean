import Mathlib
import Algebra.GcdDegree

namespace CollinsCAD

open Polynomial

/-- Collins' Theorem 2: $\deg\gcd(A,B)=k$ precisely when $\operatorname{psc}_k(A,B)\neq0$ and
    all earlier principal subresultant coefficients vanish. -/
theorem subresultant_deg_gcd_eq_least_nonzero_psc {K : Type*} [Field K] [DecidableEq K]
    (A B : Polynomial K) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (k : ℕ) :
    (EuclideanDomain.gcd A B).natDegree = k ↔
      psc A B k ≠ 0 ∧ ∀ j < k, psc A B j = 0 := by
  clear hA0 hB0
  exact natDegree_gcd_eq_iff_psc A B k

end CollinsCAD
