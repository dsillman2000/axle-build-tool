import Mathlib
import Algebra.FixedSubresultant

namespace CollinsCAD

/-- The subresultant matrix $S_j(A,B)$ of two univariate polynomials. Its rows are indexed by
    the shifts of $A$ and $B$, and its columns by the monomials of degrees
    $j,\ldots,m+n-j-1$; its determinant is the $j$-th principal subresultant coefficient. -/
def subresultantMatrix {R : Type*} [Semiring R]
    (A B : Polynomial R) (m n j : ℕ) :
    Matrix (Fin ((n - j) + (m - j))) (Fin ((n - j) + (m - j))) R :=
  Matrix.of fun r i =>
    r.addCases
      (fun p => if (p : ℕ) ≤ (i : ℕ) + j then A.coeff ((i : ℕ) + j - (p : ℕ)) else 0)
      (fun q => if (q : ℕ) ≤ (i : ℕ) + j then B.coeff ((i : ℕ) + j - (q : ℕ)) else 0)

/-- Entry in the first, `A`, row block of the legacy matrix. -/
@[simp] theorem subresultantMatrix_castAdd {R : Type*} [Semiring R]
    (A B : Polynomial R) (m n j : ℕ)
    (i : Fin ((n - j) + (m - j))) (p : Fin (n - j)) :
    subresultantMatrix A B m n j (Fin.castAdd (m - j) p) i =
      if (p : ℕ) ≤ (i : ℕ) + j then A.coeff ((i : ℕ) + j - p) else 0 := by
  simp [subresultantMatrix]

/-- Entry in the second, `B`, row block of the legacy matrix. -/
@[simp] theorem subresultantMatrix_natAdd {R : Type*} [Semiring R]
    (A B : Polynomial R) (m n j : ℕ)
    (i : Fin ((n - j) + (m - j))) (q : Fin (m - j)) :
    subresultantMatrix A B m n j (Fin.natAdd (n - j) q) i =
      if (q : ℕ) ≤ (i : ℕ) + j then B.coeff ((i : ℕ) + j - q) else 0 := by
  simp [subresultantMatrix]

/-- The $j$-th principal subresultant coefficient $\operatorname{psc}_j(A,B)$ at the actual
    degrees of $A$ and $B$.  The sign converts Mathlib's Sylvester block order to the legacy
    CollinsCAD matrix order. -/
noncomputable def psc {R : Type*} [CommRing R]
    (A B : Polynomial R) (j : ℕ) : R :=
  (-1) ^ ((A.natDegree - j) * (B.natDegree - j)) *
    Polynomial.psc A B A.natDegree B.natDegree j

/-- The actual-degree PSC is the signed fixed-bound PSC. -/
theorem psc_eq_fixed_psc {R : Type*} [CommRing R]
    (A B : Polynomial R) (j : ℕ) :
    psc A B j = (-1) ^ ((A.natDegree - j) * (B.natDegree - j)) *
      Polynomial.psc A B A.natDegree B.natDegree j := rfl

/-- Principal subresultant coefficients commute with ring homomorphisms that preserve the
    degrees of $A$ and $B$. -/
theorem psc_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Polynomial R) (j : ℕ)
    (hA : f A.leadingCoeff ≠ 0 ∨ A.natDegree = 0)
    (hB : f B.leadingCoeff ≠ 0 ∨ B.natDegree = 0) :
    f (psc A B j) = psc (A.map f) (B.map f) j := by
  have hdegA : (A.map f).natDegree = A.natDegree := Polynomial.natDegree_map_eq_iff.mpr hA
  have hdegB : (B.map f).natDegree = B.natDegree := Polynomial.natDegree_map_eq_iff.mpr hB
  simp only [psc, Polynomial.psc_map_map, map_mul, map_pow, map_neg, map_one,
    hdegA, hdegB]

/-- Actual-degree PSCs commute with coefficient maps that preserve both degrees. -/
theorem psc_map_of_natDegree_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Polynomial R) (j : ℕ)
    (hA : (A.map f).natDegree = A.natDegree)
    (hB : (B.map f).natDegree = B.natDegree) :
    f (psc A B j) = psc (A.map f) (B.map f) j := by
  simp only [psc, Polynomial.psc_map_map, map_mul, map_pow, map_neg, map_one, hA, hB]

/-- Inverse block flip on a left-block index. -/
private lemma finAddFlip_symm_castAdd {a b : ℕ} (i : Fin a) :
    (finAddFlip (m := b) (n := a)).symm (Fin.castAdd b i) = Fin.natAdd b i := by
  rw [← finAddFlip_apply_natAdd]
  exact finAddFlip.symm_apply_apply _

/-- Inverse block flip on a right-block index. -/
private lemma finAddFlip_symm_natAdd {a b : ℕ} (i : Fin b) :
    (finAddFlip (m := b) (n := a)).symm (Fin.natAdd a i) = Fin.castAdd a i := by
  rw [← finAddFlip_apply_castAdd]
  exact finAddFlip.symm_apply_apply _

/-- The legacy matrix is the Mathlib-ordered fixed matrix transposed and with
    its two row blocks exchanged. -/
theorem subresultantMatrix_eq_fixed_transpose
    {R : Type*} [Semiring R] (A B : Polynomial R) {m n j : ℕ}
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ n) :
    subresultantMatrix A B m n j =
      (Polynomial.subresultantMatrix A B m n j).transpose.reindex
        (finAddFlip (m := m - j) (n := n - j))
        (finCongr (add_comm (m - j) (n - j))) := by
  ext r i
  refine Fin.addCases ?_ ?_ r
  · intro p
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
      finAddFlip_symm_castAdd, finCongr_symm_apply]
    rw [subresultantMatrix_castAdd, Polynomial.subresultantMatrix_natAdd]
    by_cases hp : (p : ℕ) ≤ (i : ℕ) + j
    · by_cases hp' : (i : ℕ) + j ≤ (p : ℕ) + m
      · simp [hp, hp']
      · have hz : A.coeff ((i : ℕ) + j - p) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hp, hp', hz]
    · simp [hp]
  · intro q
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
      finAddFlip_symm_natAdd, finCongr_symm_apply]
    rw [subresultantMatrix_natAdd, Polynomial.subresultantMatrix_castAdd]
    by_cases hq : (q : ℕ) ≤ (i : ℕ) + j
    · by_cases hq' : (i : ℕ) + j ≤ (q : ℕ) + n
      · simp [hq, hq']
      · have hz : B.coeff ((i : ℕ) + j - q) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hq, hq', hz]
    · simp [hq]

/-- The legacy actual-degree determinant differs from the Mathlib-ordered PSC by the
    row/column block-swap sign. -/
theorem det_subresultantMatrix_eq_fixed_psc {R : Type*} [CommRing R]
    (A B : Polynomial R) (j : ℕ) :
    (subresultantMatrix A B A.natDegree B.natDegree j).det =
      (-1) ^ ((A.natDegree - j) * (B.natDegree - j)) *
        Polynomial.psc A B A.natDegree B.natDegree j := by
  rw [Polynomial.psc_def,
    subresultantMatrix_eq_fixed_transpose A B le_rfl le_rfl,
    Matrix.det_reindex, Matrix.det_transpose]
  have hcomp :
      (finCongr (add_comm (A.natDegree - j) (B.natDegree - j))).trans
        (finAddFlip (m := A.natDegree - j) (n := B.natDegree - j)).symm =
      ((finAddFlip (m := A.natDegree - j) (n := B.natDegree - j)).trans
        (finCongr (add_comm (B.natDegree - j) (A.natDegree - j)))).symm := by
    ext i
    simp
  rw [hcomp, Equiv.Perm.sign_symm,
    Polynomial.sign_finAddFlip_trans_finCongr]
  norm_cast

/-- Compatibility with the original determinant definition of `psc`. -/
theorem psc_eq_det_subresultantMatrix {R : Type*} [CommRing R]
    (A B : Polynomial R) (j : ℕ) :
    psc A B j = (subresultantMatrix A B A.natDegree B.natDegree j).det :=
  (det_subresultantMatrix_eq_fixed_psc A B j).symm

/-- The zeroth actual-degree PSC is the signed actual-degree resultant. -/
theorem psc_zero {R : Type*} [CommRing R] (A B : Polynomial R) :
    psc A B 0 = (-1) ^ (A.natDegree * B.natDegree) * Polynomial.resultant A B := by
  rw [psc, Polynomial.psc_zero]
  simp

/-- Actual-degree PSCs commute, up to the legacy block-swap sign. -/
theorem psc_comm {R : Type*} [CommRing R] (A B : Polynomial R) (j : ℕ) :
    psc A B j = (-1) ^ ((A.natDegree - j) * (B.natDegree - j)) * psc B A j := by
  rw [psc, psc, Polynomial.psc_comm]
  simp [Nat.mul_comm]

end CollinsCAD
