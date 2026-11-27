/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 as described in the file LICENSE.
Adapted for the Collins CAD demo; modified to use the local import structure.
-/

import Algebra.FixedSubresultant

/-!
# Degree drops in fixed-bound principal subresultants

Lowering a formal degree bound scales a fixed-bound PSC by a power of the coefficient at the
other bound.  The left-bound formula also records the Sylvester block-swap sign.  These identities
are unconditional because the fixed-bound matrix already truncates at its formal bounds.
-/

namespace Matrix

/-- Laplace expansion along a last row that vanishes off the diagonal. -/
private theorem det_eq_mul_det_submatrix_castSucc_of_row {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ j, j ≠ Fin.last n → A (Fin.last n) j = 0) :
    A.det = A (Fin.last n) (Fin.last n) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_row A (Fin.last n),
    Finset.sum_eq_single (Fin.last n) (fun j _ hj => by rw [h j hj]; ring) (by simp)]
  rw [Fin.succAbove_last, Fin.val_last, Even.neg_one_pow ⟨n, rfl⟩, one_mul]

end Matrix

namespace Polynomial

variable {R S : Type*} [CommRing R]

/-- The last row after increasing the right bound is supported only at the new corner. -/
private theorem lastRow_of_right_bound_succ {p q : R[X]} {m n j : ℕ}
    (hn : q.natDegree ≤ n) (hjm : j ≤ m) (hjn : j ≤ n)
    (i l : Fin ((m - j) + (n + 1 - j)))
    (hi : i.val = (m - j) + (n - j)) :
    subresultantMatrix p q m (n + 1) j i l =
      if l.val = (m - j) + (n - j) then p.coeff m else 0 := by
  induction l using Fin.addCases with
  | left l =>
    by_cases hne : ¬ i.val + j ≤ l.val + (n + 1)
    · have hne' : l.val ≠ (m - j) + (n - j) := by omega
      rw [hi] at hne
      simp [subresultantMatrix_castAdd, hi, hne, hne']
    · have hP : i.val + j ≤ l.val + (n + 1) := not_not.mp hne
      rw [hi] at hP
      have hsum : (m - j) + (n - j) + j = (m - j) + n := by omega
      rw [hsum] at hP
      have hcancel : m - j ≤ l.val + 1 := by omega
      have heq : l.val + 1 = m - j := Nat.le_antisymm l.isLt hcancel
      have hdiff : (m - j) + (n - j) + j - l.val = n + 1 := by
        rw [hsum]
        omega
      have hdeg : q.natDegree < (m - j) + (n - j) + j - l.val := by
        rw [hdiff]
        exact hn.trans_lt (Nat.lt_succ_self n)
      have hz : q.coeff ((m - j) + (n - j) + j - l.val) = 0 :=
        coeff_eq_zero_of_natDegree_lt hdeg
      have hlt : l.val < (m - j) + (n - j) :=
        lt_of_lt_of_le l.isLt (Nat.le_add_right _ _)
      have hne' : l.val ≠ (m - j) + (n - j) := by omega
      simp [subresultantMatrix_castAdd, hi, hz, hne']
  | right l =>
    by_cases h : l.val = n - j
    · rw [subresultantMatrix_natAdd, hi]
      simp only [Fin.val_natAdd, h, ite_true]
      have hcoeff : (m - j) + (n - j) + j - (n - j) = m := by omega
      rw [hcoeff]
      have hlow : n - j ≤ (m - j) + (n - j) + j := by omega
      have hupp : (m - j) + (n - j) + j ≤ n - j + m := by omega
      simp [hlow, hupp]
    · have hne : ¬ i.val + j ≤ l.val + m := by omega
      rw [hi] at hne
      simp [subresultantMatrix_natAdd, hi, h, hne]

/-- Increasing the right formal bound by one scales the PSC by the left-bound coefficient. -/
theorem psc_succ_right {p q : R[X]} {m n j : ℕ}
    (hn : q.natDegree ≤ n) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q m (n + 1) j = p.coeff m * psc p q m n j := by
  classical
  let d := (m - j) + (n - j)
  have hd : (m - j) + (n + 1 - j) = d + 1 := by dsimp [d]; omega
  let e := finCongr hd
  let M := (subresultantMatrix p q m (n + 1) j).reindex e e
  have hlast (l : Fin (d + 1)) :
      M (Fin.last d) l = if l = Fin.last d then p.coeff m else 0 := by
    simpa only [M, Matrix.reindex_apply, Matrix.submatrix_apply, e, finCongr_apply,
      finCongr_symm, Fin.val_cast, Fin.val_last, Fin.ext_iff] using
      lastRow_of_right_bound_succ hn hjm hjn (e.symm (Fin.last d)) (e.symm l) rfl
  have hminor : M.submatrix Fin.castSucc Fin.castSucc = subresultantMatrix p q m n j := by
    ext i l
    simp only [Matrix.submatrix_apply, M, Matrix.reindex_apply, Matrix.submatrix_apply]
    induction l using Fin.addCases with
    | left l =>
      have hl : e.symm (Fin.castAdd (n - j) l).castSucc =
          Fin.castAdd (n + 1 - j) l := by ext; simp [e]
      rw [hl]
      have hv : (e.symm i.castSucc : ℕ) = i := rfl
      by_cases hlower : l.val ≤ i.val + j
      · by_cases hlow : i.val + j ≤ l.val + n
        · have hhigh : i.val + j ≤ l.val + (n + 1) := by omega
          simp only [subresultantMatrix_castAdd, hv, hlower, hlow, hhigh, and_self]
        · by_cases hhigh : i.val + j ≤ l.val + (n + 1)
          · have hcoeff : i.val + j - l.val = n + 1 := by omega
            have hz : q.coeff (n + 1) = 0 :=
              coeff_eq_zero_of_natDegree_lt (hn.trans_lt (Nat.lt_succ_self n))
            simp only [subresultantMatrix_castAdd, hv, hlower, hlow]
            rw [hcoeff, hz]
            simp [hhigh]
          · simp only [subresultantMatrix_castAdd, hv, hlower, hlow, hhigh]
      · simp only [subresultantMatrix_castAdd, hv, hlower, false_and, ite_false]
    | right l =>
      have hle : n - j ≤ n + 1 - j := by omega
      have hl : e.symm (Fin.natAdd (m - j) l).castSucc =
          Fin.natAdd (m - j) (Fin.castLE hle l) := by ext; simp [e]
      rw [hl]
      have hv : (e.symm i.castSucc : ℕ) = i := rfl
      simp only [subresultantMatrix_natAdd, hv, Fin.val_castLE]
  have hdet : psc p q m (n + 1) j = M.det := by
    simp only [M, Matrix.det_reindex_self, psc_def]
  rw [hdet, Matrix.det_eq_mul_det_submatrix_castSucc_of_row M (by
    intro l hl
    simp [hlast, hl]), hlast, hminor]
  simp [psc_def]

/-- Lowering an oversized right bound scales the PSC by the corresponding coefficient power. -/
theorem psc_eq_coeff_pow_mul_of_right_degree_drop {p q : R[X]} {m n N j : ℕ}
    (hn : q.natDegree ≤ n) (hN : n ≤ N) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q m N j = p.coeff m ^ (N - n) * psc p q m n j := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [psc_succ_right (hn.trans hN) hjm (hjn.trans hN), ih]
    have hgap : N + 1 - n = (N - n) + 1 := by omega
    rw [hgap, pow_succ]
    ring

/-- Lowering an oversized left bound scales the PSC by a coefficient power and the block-swap
sign. -/
theorem psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop {p q : R[X]} {m M n j : ℕ}
    (hm : p.natDegree ≤ m) (hM : m ≤ M) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q M n j = (-1) ^ ((M - m) * (n - j)) *
      q.coeff n ^ (M - m) * psc p q m n j := by
  have hgap : M - j = (M - m) + (m - j) := by omega
  calc
    psc p q M n j = (-1) ^ ((M - j) * (n - j)) *
        (q.coeff n ^ (M - m) * psc q p n m j) := by
      rw [psc_comm p q M n j,
        psc_eq_coeff_pow_mul_of_right_degree_drop hm hM hjn hjm]
    _ = _ := by
      rw [psc_comm p q m n j, hgap, add_mul, pow_add]
      ring

/-- If both actual degrees are strictly below their formal bounds, every strict PSC vanishes. -/
theorem psc_eq_zero_of_natDegree_lt_bounds {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree < m) (hn : q.natDegree < n) (hj : j < min m n) :
    psc p q m n j = 0 := by
  have hnpos : 0 < n := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  rw [psc_succ_right (by omega) (by omega) (by omega),
    coeff_eq_zero_of_natDegree_lt hm, zero_mul]

/-- Fixed-bound mapping commutes with a right degree drop. -/
theorem map_psc_of_right_degree_drop {S : Type*} [CommRing S] (f : R →+* S)
    {p q : R[X]} {m n N j : ℕ} (hn : (q.map f).natDegree ≤ n)
    (hN : n ≤ N) (hjm : j ≤ m) (hjn : j ≤ n) :
    f (psc p q m N j) = f (p.coeff m) ^ (N - n) *
      psc (p.map f) (q.map f) m n j := by
  rw [← psc_map_map, psc_eq_coeff_pow_mul_of_right_degree_drop hn hN hjm hjn, coeff_map]

/-- Fixed-bound mapping commutes with a left degree drop, including its sign. -/
theorem map_psc_of_left_degree_drop {S : Type*} [CommRing S] (f : R →+* S)
    {p q : R[X]} {m M n j : ℕ} (hm : (p.map f).natDegree ≤ m)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j ≤ n) :
    f (psc p q M n j) = (-1) ^ ((M - m) * (n - j)) *
      f (q.coeff n) ^ (M - m) * psc (p.map f) (q.map f) m n j := by
  rw [← psc_map_map,
    psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hm hM hjm hjn, coeff_map]

end Polynomial
