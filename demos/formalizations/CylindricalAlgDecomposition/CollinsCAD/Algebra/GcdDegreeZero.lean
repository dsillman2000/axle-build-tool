import Mathlib
import Algebra.GcdDegree

namespace CollinsCAD

open Polynomial

/-- If $j<\deg\gcd(A,B)$ then $\operatorname{psc}_j(A,B)=0$. -/
theorem psc_eq_zero_of_lt_gcd {K : Type*} [Field K] [DecidableEq K]
    (A B : Polynomial K) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (j : ℕ)
    (hjA : j < A.natDegree) (hjB : j < B.natDegree)
    (hj : j < (EuclideanDomain.gcd A B).natDegree) :
    psc A B j = 0 := by
  exact psc_eq_zero_of_lt_natDegree_gcd A B j hj

end CollinsCAD
