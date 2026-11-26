import Mathlib
import Algebra.SubresultantBezout

namespace CollinsCAD

open Polynomial

/-- A polynomial in `degreeLT K d` has natural degree $<d$ when it is nonzero. -/
theorem natDegree_lt_of_mem_degreeLT {K : Type*} [Field K] {d : ℕ} {p : Polynomial K}
    (hp : p ∈ Polynomial.degreeLT K d) (hp0 : p ≠ 0) : p.natDegree < d := by
  have hdeg := Polynomial.mem_degreeLT.mp hp
  rw [Polynomial.degree_eq_natDegree hp0] at hdeg
  exact_mod_cast hdeg

/-- The only polynomial of degree $<0$ is zero. -/
theorem eq_zero_of_mem_degreeLT_zero {K : Type*} [Field K] {p : Polynomial K}
    (hp : p ∈ Polynomial.degreeLT K 0) : p = 0 := by
  by_contra hp0
  have := natDegree_lt_of_mem_degreeLT hp hp0
  omega

/-- At the index equal to $\deg\gcd(A,B)$, the principal subresultant coefficient is nonzero. -/
theorem psc_ne_zero_of_gcd_eq {K : Type*} [Field K] [DecidableEq K]
    (A B : Polynomial K) (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hjA : (EuclideanDomain.gcd A B).natDegree ≤ A.natDegree)
    (hjB : (EuclideanDomain.gcd A B).natDegree ≤ B.natDegree)
    (hj : (EuclideanDomain.gcd A B).natDegree = j) :
    psc A B j ≠ 0 := by
  classical
  let h := EuclideanDomain.gcd A B
  have hh0 : h ≠ 0 := by
    intro hz
    have hz' : EuclideanDomain.gcd A B = 0 := by simpa [h] using hz
    have hdvd := EuclideanDomain.gcd_dvd_right A B
    rw [hz'] at hdvd
    exact hB0 (zero_dvd_iff.mp hdvd)
  intro hpsc
  obtain ⟨u, v, huv, hzero⟩ := (psc_eq_zero_iff_exists_uv A B j).mp hpsc
  let bound := A.natDegree + B.natDegree - j
  by_cases hbound0 : bound = 0
  · have hAj : A.natDegree - j = 0 := by omega
    have hBj : B.natDegree - j = 0 := by omega
    have uu : u.1 = 0 := by
      apply eq_zero_of_mem_degreeLT_zero
      rw [← hBj]
      exact u.2
    have vv : v.1 = 0 := by
      apply eq_zero_of_mem_degreeLT_zero
      rw [← hAj]
      exact v.2
    exact (huv.elim (fun hu => hu (by simpa using uu)) (fun hv => hv (by simpa using vv))).elim
  have hbound_pos : 0 < bound := Nat.pos_of_ne_zero hbound0
  have hcoeff_low : ∀ N, j ≤ N → N < bound → (u.1 * A + v.1 * B).coeff N = 0 := by
    intro N hNj hN
    have hi : N - j < (B.natDegree - j) + (A.natDegree - j) := by omega
    have hc := congrFun hzero ⟨N - j, hi⟩
    simpa [coeffMap, hNj] using hc
  have huA_lt : (u.1 * A).natDegree < bound := by
    by_cases hu0 : u.1 = 0
    · simpa [hu0] using hbound_pos
    · have hu_nd := natDegree_lt_of_mem_degreeLT u.2 hu0
      calc
        (u.1 * A).natDegree ≤ u.1.natDegree + A.natDegree := Polynomial.natDegree_mul_le
        _ < bound := by omega
  have hvB_lt : (v.1 * B).natDegree < bound := by
    by_cases hv0 : v.1 = 0
    · simpa [hv0] using hbound_pos
    · have hv_nd := natDegree_lt_of_mem_degreeLT v.2 hv0
      calc
        (v.1 * B).natDegree ≤ v.1.natDegree + B.natDegree := Polynomial.natDegree_mul_le
        _ < bound := by omega
  let P := u.1 * A + v.1 * B
  have hP_lt : P.natDegree < bound := by
    dsimp [P]
    exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt huA_lt hvB_lt)
  have hPzero_or : P = 0 ∨ P.natDegree < j := by
    by_cases hP0 : P = 0
    · exact Or.inl hP0
    · right
      by_contra hPj
      have hle : j ≤ P.natDegree := by omega
      have hcoeff : P.coeff P.natDegree = 0 := by
        by_cases hNbig : bound ≤ P.natDegree
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hP_lt hNbig)
        · exact hcoeff_low P.natDegree hle (by omega)
      have hlead : P.coeff P.natDegree ≠ 0 := by
        simpa only [Polynomial.leadingCoeff] using Polynomial.leadingCoeff_ne_zero.mpr hP0
      exact hlead hcoeff
  have hhdvd : h ∣ P := dvd_add (dvd_mul_of_dvd_right (EuclideanDomain.gcd_dvd_left A B) u.1)
    (dvd_mul_of_dvd_right (EuclideanDomain.gcd_dvd_right A B) v.1)
  have hP0 : P = 0 := by
    rcases hPzero_or with hP0 | hPlt
    · exact hP0
    · by_contra hPne
      have hkdeg : h.natDegree ≤ P.natDegree := Polynomial.natDegree_le_of_dvd hhdvd hPne
      have hkj : h.natDegree = j := by simpa [h] using hj
      omega
  obtain ⟨A', hAeq⟩ := EuclideanDomain.gcd_dvd_left A B
  obtain ⟨B', hBeq⟩ := EuclideanDomain.gcd_dvd_right A B
  have hA'0 : A' ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hAeq
    exact hA0 hAeq
  have hcop : IsCoprime A' B' := by
    refine ⟨EuclideanDomain.gcdA A B, EuclideanDomain.gcdB A B, ?_⟩
    apply mul_left_cancel₀ hh0
    calc
      h * (EuclideanDomain.gcdA A B * A' + EuclideanDomain.gcdB A B * B') =
          EuclideanDomain.gcdA A B * (h * A') + EuclideanDomain.gcdB A B * (h * B') := by ring
      _ = EuclideanDomain.gcdA A B * A + EuclideanDomain.gcdB A B * B := by rw [← hAeq, ← hBeq]
      _ = h := by simpa [h, mul_comm] using (EuclideanDomain.gcd_eq_gcd_ab A B).symm
      _ = h * 1 := by simp
  have hcomb : u.1 * A' + v.1 * B' = 0 := by
    apply mul_left_cancel₀ hh0
    calc
      h * (u.1 * A' + v.1 * B') = u.1 * (h * A') + v.1 * (h * B') := by ring
      _ = u.1 * A + v.1 * B := by rw [← hAeq, ← hBeq]
      _ = 0 := by simpa [P] using hP0
      _ = h * 0 := by simp
  have hvB' : A' ∣ v.1 * B' := by
    rw [← neg_eq_iff_add_eq_zero] at hcomb
    exact ⟨-u.1, by simpa [mul_comm] using hcomb.symm⟩
  have hvdiv : A' ∣ v.1 := hcop.dvd_of_dvd_mul_right hvB'
  have hA'deg : A'.natDegree = A.natDegree - h.natDegree := by
    rw [hAeq, Polynomial.natDegree_mul hh0 hA'0]
    omega
  have hv0 : v.1 = 0 := by
    by_cases hvne : (v.1 : Polynomial K) = 0
    · exact hvne
    · have hvnd : v.1.natDegree < A.natDegree - j := by
        exact natDegree_lt_of_mem_degreeLT v.2 hvne
      have hA'deg' : A'.natDegree = A.natDegree - j := by
        rw [hA'deg, hj]
      have hd := Polynomial.natDegree_le_of_dvd hvdiv hvne
      rw [hA'deg'] at hd
      omega
  have hu0 : u.1 = 0 := by
    have hmul : u.1 * A' = 0 := by simpa [hv0] using hcomb
    exact (mul_eq_zero.mp hmul).resolve_right hA'0
  exact (huv.elim (fun hu => hu (by simpa using hu0)) (fun hv => hv (by simpa using hv0))).elim

end CollinsCAD
