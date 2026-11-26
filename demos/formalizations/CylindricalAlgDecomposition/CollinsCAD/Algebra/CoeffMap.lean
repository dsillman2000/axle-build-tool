import Mathlib
import Algebra.Subresultant

namespace CollinsCAD

open Polynomial

/-- The linear map sending a pair of short polynomials $(u,v)$ to the coefficients of
    $uA+vB$ in degrees $j,\ldots,m+n-j-1$. -/
noncomputable def coeffMap {K : Type*} [Field K]
    (A B : Polynomial K) (m n j : ℕ) :
    (Polynomial.degreeLT K (n - j) × Polynomial.degreeLT K (m - j)) →ₗ[K]
      (Fin ((n - j) + (m - j)) → K) where
  toFun uv i := (uv.1.1 * A + uv.2.1 * B).coeff ((i : ℕ) + j)
  map_add' u v := by
    ext i
    simp [add_mul, add_assoc, add_comm, add_left_comm]
  map_smul' c u := by
    ext i
    simp [mul_add]

/-- The matrix of `coeffMap` in the monomial bases is the transpose of the subresultant matrix. -/
theorem coeffMap_toMatrix {K : Type*} [Field K]
    (A B : Polynomial K) (m n j : ℕ) :
    (coeffMap A B m n j).toMatrix
        (Polynomial.degreeLT.basisProd K (n - j) (m - j))
        (Pi.basisFun K (Fin ((n - j) + (m - j)))) =
      (subresultantMatrix A B m n j).transpose := by
  ext i r
  refine Fin.addCases ?_ ?_ r
  · intro p
    simp [coeffMap, subresultantMatrix, LinearMap.toMatrix_apply,
      Polynomial.degreeLT.basisProd_castAdd, Polynomial.degreeLT.basis_val,
      Polynomial.coeff_X_pow_mul']
  · intro q
    simp [coeffMap, subresultantMatrix, LinearMap.toMatrix_apply,
      Polynomial.degreeLT.basisProd_natAdd, Polynomial.degreeLT.basis_val,
      Polynomial.coeff_X_pow_mul']

end CollinsCAD
