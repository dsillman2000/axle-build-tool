import Mathlib

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

/-- The $j$-th principal subresultant coefficient $\operatorname{psc}_j(A,B)$, the determinant of
    the subresultant matrix formed from the actual degrees of $A$ and $B$. -/
noncomputable def psc {R : Type*} [CommRing R]
    (A B : Polynomial R) (j : ℕ) : R :=
  (subresultantMatrix A B A.natDegree B.natDegree j).det

/-- Principal subresultant coefficients commute with ring homomorphisms that preserve the
    degrees of $A$ and $B$. -/
theorem psc_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Polynomial R) (j : ℕ)
    (hA : f A.leadingCoeff ≠ 0 ∨ A.natDegree = 0)
    (hB : f B.leadingCoeff ≠ 0 ∨ B.natDegree = 0) :
    f (psc A B j) = psc (A.map f) (B.map f) j := by
  rw [psc, psc, RingHom.map_det]
  have hdegA : (A.map f).natDegree = A.natDegree := Polynomial.natDegree_map_eq_iff.mpr hA
  have hdegB : (B.map f).natDegree = B.natDegree := Polynomial.natDegree_map_eq_iff.mpr hB
  rw [hdegA, hdegB]
  congr 1
  ext r i
  refine Fin.addCases ?_ ?_ r
  · intro p
    by_cases h : (p : ℕ) ≤ (i : ℕ) + j <;> simp [subresultantMatrix, h]
  · intro q
    by_cases h : (q : ℕ) ≤ (i : ℕ) + j <;> simp [subresultantMatrix, h]

end CollinsCAD
