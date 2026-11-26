import Mathlib
import Algebra.GcdDegree

namespace CollinsCAD

open Polynomial

/-- If every principal subresultant coefficient below the minimum degree
    vanishes, then the GCD attains that minimum degree. -/
theorem natDegree_gcd_eq_of_psc_zero_lt {K : Type*} [Field K] [DecidableEq K]
    (A B : Polynomial K) (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hzeros : ∀ j < min A.natDegree B.natDegree, psc A B j = 0) :
    (EuclideanDomain.gcd A B).natDegree = min A.natDegree B.natDegree := by
  have hdA : (EuclideanDomain.gcd A B).natDegree ≤ A.natDegree :=
    Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left A B) hA0
  have hdB : (EuclideanDomain.gcd A B).natDegree ≤ B.natDegree :=
    Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right A B) hB0
  have hle : (EuclideanDomain.gcd A B).natDegree ≤ min A.natDegree B.natDegree :=
    le_min hdA hdB
  by_contra hne
  have hlt : (EuclideanDomain.gcd A B).natDegree < min A.natDegree B.natDegree :=
    lt_of_le_of_ne hle hne
  have hpsc := psc_ne_zero_of_gcd_eq A B hA0 hB0 hdA hdB rfl
  exact hpsc (hzeros _ hlt)

end CollinsCAD
