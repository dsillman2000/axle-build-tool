import Mathlib
import Algebra.Subresultant

namespace CollinsCAD

/-- The vanishing of the $j$-th subresultant coefficient is equivalent to the existence of a
    nonzero coefficient vector annihilating the subresultant matrix. -/
theorem psc_eq_zero_iff_exists_vec {K : Type*} [Field K]
    (A B : Polynomial K) (j : ℕ) :
    psc A B j = 0 ↔
      ∃ c : Fin ((B.natDegree - j) + (A.natDegree - j)) → K,
        c ≠ 0 ∧
          Matrix.vecMul c (subresultantMatrix A B A.natDegree B.natDegree j) = 0 := by
  rw [psc]
  exact (Matrix.exists_vecMul_eq_zero_iff (M := subresultantMatrix A B A.natDegree B.natDegree j)).symm

end CollinsCAD
