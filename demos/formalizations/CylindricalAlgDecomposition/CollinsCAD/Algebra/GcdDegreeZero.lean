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
  classical
  let h := EuclideanDomain.gcd A B
  have hh0 : h ≠ 0 := by
    intro hz
    have hz' : EuclideanDomain.gcd A B = 0 := by simpa [h] using hz
    have hdvd := EuclideanDomain.gcd_dvd_left A B
    rw [hz'] at hdvd
    exact hA0 (zero_dvd_iff.mp hdvd)
  obtain ⟨A', hAeq⟩ := EuclideanDomain.gcd_dvd_left A B
  obtain ⟨B', hBeq⟩ := EuclideanDomain.gcd_dvd_right A B
  have hA'0 : A' ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hAeq
    exact hA0 hAeq
  have hB'0 : B' ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hBeq
    exact hB0 hBeq
  have hA'deg : A'.natDegree = A.natDegree - h.natDegree := by
    rw [hAeq, Polynomial.natDegree_mul hh0 hA'0]
    omega
  have hB'deg : B'.natDegree = B.natDegree - h.natDegree := by
    rw [hBeq, Polynomial.natDegree_mul hh0 hB'0]
    omega
  let t := h.natDegree - j - 1
  have hk : (EuclideanDomain.gcd A B).natDegree = h.natDegree := rfl
  let up : Polynomial K := B' * X ^ t
  let vp : Polynomial K := -A' * X ^ t
  have hu0 : up ≠ 0 := by
    dsimp [up]
    exact mul_ne_zero hB'0 (pow_ne_zero _ Polynomial.X_ne_zero)
  have hv0 : vp ≠ 0 := by
    dsimp [vp]
    exact mul_ne_zero (neg_ne_zero.mpr hA'0) (pow_ne_zero _ Polynomial.X_ne_zero)
  have hk_le_A : h.natDegree ≤ A.natDegree :=
    Polynomial.natDegree_le_of_dvd (by simpa [h] using EuclideanDomain.gcd_dvd_left A B) hA0
  have hk_le_B : h.natDegree ≤ B.natDegree :=
    Polynomial.natDegree_le_of_dvd (by simpa [h] using EuclideanDomain.gcd_dvd_right A B) hB0
  have hAeq' : A = h * A' := by simpa [h] using hAeq
  have hBeq' : B = h * B' := by simpa [h] using hBeq
  have hupdeg : up.natDegree < B.natDegree - j := by
    dsimp [up]
    rw [Polynomial.natDegree_mul hB'0 (pow_ne_zero _ Polynomial.X_ne_zero),
      Polynomial.natDegree_X_pow]
    rw [hB'deg]
    dsimp [t]
    omega
  have hvpdeg : vp.natDegree < A.natDegree - j := by
    dsimp [vp]
    rw [Polynomial.natDegree_mul (neg_ne_zero.mpr hA'0) (pow_ne_zero _ Polynomial.X_ne_zero),
      Polynomial.natDegree_X_pow, Polynomial.natDegree_neg, hA'deg]
    dsimp [t]
    omega
  have humem : up ∈ Polynomial.degreeLT K (B.natDegree - j) := by
    rw [Polynomial.mem_degreeLT]
    rw [Polynomial.degree_eq_natDegree hu0]
    exact_mod_cast hupdeg
  have hvmem : vp ∈ Polynomial.degreeLT K (A.natDegree - j) := by
    rw [Polynomial.mem_degreeLT]
    rw [Polynomial.degree_eq_natDegree hv0]
    exact_mod_cast hvpdeg
  refine (psc_eq_zero_iff_exists_uv A B j).mpr ⟨⟨up, humem⟩, ⟨vp, hvmem⟩, ?_, ?_⟩
  · exact Or.inl (by simpa using hu0)
  · have hlin : up * A + vp * B = 0 := by
      dsimp [up, vp]
      rw [hAeq', hBeq']
      ring_nf
    ext i
    simpa [coeffMap] using congrArg (fun q : Polynomial K => q.coeff ((i : ℕ) + j)) hlin

end CollinsCAD
