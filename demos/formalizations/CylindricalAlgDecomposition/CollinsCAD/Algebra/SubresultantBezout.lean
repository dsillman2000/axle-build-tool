import Mathlib
import Algebra.Subresultant
import Algebra.GcdPsc

namespace CollinsCAD

open Polynomial
open scoped BigOperators

/-- A nontrivial short polynomial relation is a kernel vector of the actual-degree subresultant
    matrix, so its determinant vanishes. -/
theorem psc_eq_zero_of_mul_add_mul_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    {A B u v : Polynomial R} {j : ℕ}
    (hu : u.degree < (B.natDegree - j : ℕ))
    (hv : v.degree < (A.natDegree - j : ℕ))
    (hrel : u * A + v * B = 0) (hne : u ≠ 0 ∨ v ≠ 0) :
    psc A B j = 0 := by
  have hfixed := Polynomial.psc_eq_zero_of_mul_add_mul_eq_zero
    (p := A) (q := B) (A := v) (B := u) le_rfl le_rfl hv hu
    (by simpa [add_comm] using hrel) (by simpa [or_comm] using hne)
  rw [psc_eq_fixed_psc, hfixed, mul_zero]

/-- Compatibility linear map sending a pair of short polynomials $(u,v)$ to the coefficients
    of $uA+vB$ in degrees $j,\ldots,m+n-j-1$. -/
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

/-- Compatibility matrix identification for `coeffMap`. -/
theorem coeffMap_toMatrix {K : Type*} [Field K]
    (A B : Polynomial K) (m n j : ℕ) :
    (coeffMap A B m n j).toMatrix
        (Polynomial.degreeLT.basisProd K (n - j) (m - j))
        (Pi.basisFun K (Fin ((n - j) + (m - j)))) =
      (CollinsCAD.subresultantMatrix A B m n j).transpose := by
  ext i r
  refine Fin.addCases ?_ ?_ r
  · intro p
    simp [coeffMap, CollinsCAD.subresultantMatrix, LinearMap.toMatrix_apply,
      Polynomial.degreeLT.basisProd_castAdd, Polynomial.degreeLT.basis_val,
      Polynomial.coeff_X_pow_mul']
  · intro q
    simp [coeffMap, CollinsCAD.subresultantMatrix, LinearMap.toMatrix_apply,
      Polynomial.degreeLT.basisProd_natAdd, Polynomial.degreeLT.basis_val,
      Polynomial.coeff_X_pow_mul']

/-- The coordinates of the coefficient map agree with `vecMul` against the subresultant matrix. -/
theorem coeffMap_eq_vecMul {K : Type*} [Field K]
    (A B : Polynomial K) (m n j : ℕ)
    (uv : Polynomial.degreeLT K (n - j) × Polynomial.degreeLT K (m - j)) :
    coeffMap A B m n j uv =
      Matrix.vecMul ((Polynomial.degreeLT.basisProd K (n - j) (m - j)).equivFun uv)
        (CollinsCAD.subresultantMatrix A B m n j) := by
  let b := Polynomial.degreeLT.basisProd K (n - j) (m - j)
  have hb : ∀ r i, coeffMap A B m n j (b r) i = CollinsCAD.subresultantMatrix A B m n j r i := by
    intro r i
    have h := congrFun (congrFun (coeffMap_toMatrix A B m n j) i) r
    simpa [LinearMap.toMatrix_apply] using h
  ext i
  calc
    coeffMap A B m n j uv i =
        coeffMap A B m n j (∑ r, (b.repr uv) r • b r) i := by
          exact congrArg (fun z => coeffMap A B m n j z i) (b.sum_repr uv).symm
    _ = ∑ r, (b.repr uv) r * coeffMap A B m n j (b r) i := by
          rw [map_sum]
          simp
    _ = ∑ r, b.equivFun uv r * CollinsCAD.subresultantMatrix A B m n j r i := by
          simp [hb]
    _ = Matrix.vecMul (b.equivFun uv) (CollinsCAD.subresultantMatrix A B m n j) i := by
          simp [Matrix.vecMul, dotProduct]

/-- A principal subresultant coefficient vanishes exactly when there is a nonzero pair
    $(u,v)$ with $\deg u<n-j$, $\deg v<m-j$ and all coefficients of $uA+vB$ in degrees
    $j,\ldots,m+n-j-1$ zero. -/
theorem psc_eq_zero_iff_exists_uv {K : Type*} [Field K]
    (A B : Polynomial K) (j : ℕ) :
    psc A B j = 0 ↔
      ∃ u : Polynomial.degreeLT K (B.natDegree - j),
        ∃ v : Polynomial.degreeLT K (A.natDegree - j),
          (u.1 ≠ 0 ∨ v.1 ≠ 0) ∧
            coeffMap A B A.natDegree B.natDegree j (u, v) = 0 := by
  let b := Polynomial.degreeLT.basisProd K (B.natDegree - j) (A.natDegree - j)
  rw [psc_eq_det_subresultantMatrix]
  constructor
  · intro hdet
    obtain ⟨c, hcne, hcvec⟩ :=
      (Matrix.exists_vecMul_eq_zero_iff
        (M := CollinsCAD.subresultantMatrix A B A.natDegree B.natDegree j)).mpr hdet
    let uv := b.equivFun.symm c
    have huv_eq : b.equivFun uv = c := by
      dsimp [uv]
      exact (b.equivFun).apply_symm_apply c
    refine ⟨uv.1, uv.2, ?_, ?_⟩
    · by_cases hu : uv.1 = 0
      · right
        intro hv
        have huv0 : uv = 0 := by
          ext <;> simp [hu, hv]
        exact hcne (by simpa [huv_eq] using congrArg b.equivFun huv0)
      · exact Or.inl (by simpa using hu)
    · rw [coeffMap_eq_vecMul, huv_eq]
      exact hcvec
  · rintro ⟨u, v, huv, hzero⟩
    have hcne : b.equivFun (u, v) ≠ 0 := by
      intro hc
      have hpair : (u, v) = 0 := by simpa using congrArg b.equivFun.symm hc
      have hu0 : u = 0 := by simpa using congrArg Prod.fst hpair
      have hv0 : v = 0 := by simpa using congrArg Prod.snd hpair
      exact huv.elim (fun h => h (by simpa using hu0)) (fun h => h (by simpa using hv0))
    apply (Matrix.exists_vecMul_eq_zero_iff
      (M := CollinsCAD.subresultantMatrix A B A.natDegree B.natDegree j)).mp
    refine ⟨b.equivFun (u, v), hcne, ?_⟩
    rw [← coeffMap_eq_vecMul]
    exact hzero

end CollinsCAD
