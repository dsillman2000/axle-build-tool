import Mathlib
import Algebra.DistinctRoots

namespace CollinsCAD

open Polynomial

/-- Collins' Theorem 3: the number of distinct complex roots of a nonzero real polynomial is
    $\deg A-\deg\gcd(A,A')$. -/
theorem roots_card_distinct_eq_sub_deg_gcd_deriv (A : Polynomial ℝ) (hA0 : A ≠ 0) :
    ((A.map (algebraMap ℝ ℂ)).roots.toFinset.card) =
      A.natDegree - (EuclideanDomain.gcd A A.derivative).natDegree := by
  let φ : ℝ →+* ℂ := algebraMap ℝ ℂ
  let P := A.map φ
  have hinj : Function.Injective φ := (algebraMap ℝ ℂ).injective
  have hP0 : P ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff hinj).2 hA0
  have hnat : P.natDegree = A.natDegree := Polynomial.natDegree_map_eq_of_injective hinj A
  have hder : P.derivative = A.derivative.map φ := by
    dsimp [P]
    simp
  have hgcd : EuclideanDomain.gcd P P.derivative =
      (EuclideanDomain.gcd A A.derivative).map φ := by
    rw [hder]
    simpa [φ, P] using (Polynomial.gcd_map φ (p := A) (q := A.derivative))
  have hgcdnat : (EuclideanDomain.gcd P P.derivative).natDegree =
      (EuclideanDomain.gcd A A.derivative).natDegree := by
    rw [hgcd]
    exact Polynomial.natDegree_map_eq_of_injective hinj (EuclideanDomain.gcd A A.derivative)
  have h := card_roots_toFinset_eq_sub_gcd (P := P) hP0
  rw [hnat, hgcdnat] at h
  simpa [P, φ] using h

end CollinsCAD
