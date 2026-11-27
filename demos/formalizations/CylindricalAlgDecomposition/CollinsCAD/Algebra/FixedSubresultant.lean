/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 as described in the file LICENSE.
Adapted for the Collins CAD demo; modified to use the local import structure.
-/

import Mathlib
import Mathlib.GroupTheory.Perm.Fin

/-!
# Fixed-bound principal subresultants

The degree bounds are part of the data and are not recomputed after coefficient
specialization.  The matrix uses Mathlib's Sylvester block order, so its
zeroth determinant is `Polynomial.resultant` without an additional sign.
-/

namespace Polynomial

open scoped BigOperators

variable {R S : Type*}

/-- A shifted coefficient, truncated at a formal degree bound. -/
theorem coeff_X_pow_mul_of_natDegree_le [Semiring R] {p : R[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (l d : ℕ) :
    (X ^ l * p).coeff d =
      if l ≤ d ∧ d ≤ l + n then p.coeff (d - l) else 0 := by
  rw [coeff_X_pow_mul']
  by_cases hld : l ≤ d
  · by_cases hdn : d ≤ l + n
    · simp [hld, hdn]
    · have hlt : n < d - l := by omega
      simp [hld, hdn, coeff_eq_zero_of_natDegree_lt (hp.trans_lt hlt)]
  · simp [hld]

/-- The fixed-bound principal subresultant matrix in Mathlib Sylvester order. -/
def subresultantMatrix [Semiring R] (p q : R[X]) (m n j : ℕ) :
    Matrix (Fin ((m - j) + (n - j))) (Fin ((m - j) + (n - j))) R :=
  Matrix.of fun i k =>
    k.addCases
      (fun k => if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + n then
        q.coeff (i.val + j - k.val) else 0)
      (fun k => if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + m then
        p.coeff (i.val + j - k.val) else 0)

/-- Entry in the first, `q`, column block. -/
theorem subresultantMatrix_castAdd [Semiring R]
    (p q : R[X]) (m n j : ℕ)
    (i : Fin ((m - j) + (n - j))) (k : Fin (m - j)) :
    subresultantMatrix p q m n j i (Fin.castAdd (n - j) k) =
      if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + n then
        q.coeff (i.val + j - k.val) else 0 := by
  simp [subresultantMatrix]

/-- Entry in the second, `p`, column block. -/
theorem subresultantMatrix_natAdd [Semiring R]
    (p q : R[X]) (m n j : ℕ)
    (i : Fin ((m - j) + (n - j))) (k : Fin (n - j)) :
    subresultantMatrix p q m n j i (Fin.natAdd (m - j) k) =
      if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + m then
        p.coeff (i.val + j - k.val) else 0 := by
  simp [subresultantMatrix]

/-- At formal bounds dominating the degrees, entries are shifted coefficients. -/
theorem subresultantMatrix_apply_eq_coeff [Semiring R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (j : ℕ) (i k : Fin ((m - j) + (n - j))) :
    subresultantMatrix p q m n j i k =
      k.addCases (fun k => (X ^ k.val * q).coeff (i.val + j))
        (fun k => (X ^ k.val * p).coeff (i.val + j)) := by
  induction k using Fin.addCases <;>
    simp [subresultantMatrix, coeff_X_pow_mul_of_natDegree_le hm,
      coeff_X_pow_mul_of_natDegree_le hn]

/-- At index zero this is Mathlib's Sylvester matrix. -/
theorem subresultantMatrix_zero [Semiring R] (p q : R[X]) (m n : ℕ) :
    subresultantMatrix p q m n 0 = p.sylvester q m n := by
  ext i k
  induction k using Fin.addCases <;> simp [subresultantMatrix, Polynomial.sylvester]

/-- Fixed-bound matrices commute with coefficient maps. -/
theorem subresultantMatrix_map_map [Semiring R] [Semiring S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    subresultantMatrix (p.map f) (q.map f) m n j =
      f.mapMatrix (subresultantMatrix p q m n j) := by
  ext i k
  induction k using Fin.addCases <;> simp [subresultantMatrix, apply_ite f]

/-- One row reads a coefficient of `A * q + B * p`. -/
private theorem coefficientRow_dotProduct [CommSemiring R] [DecidableEq R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (a b d : ℕ) (v : Fin (a + b) → R) :
    (Fin.addCases
      (fun l : Fin a => if (l : ℕ) ≤ d ∧ d ≤ l.val + n then
        q.coeff (d - l.val) else 0)
      (fun l : Fin b => if (l : ℕ) ≤ d ∧ d ≤ l.val + m then
        p.coeff (d - l.val) else 0))
      ⬝ᵥ v =
      (ofFn a (fun l => v (Fin.castAdd b l)) * q +
        ofFn b (fun l => v (Fin.natAdd a l)) * p).coeff d := by
  simp_rw [← coeff_X_pow_mul_of_natDegree_le hn,
    ← coeff_X_pow_mul_of_natDegree_le hm]
  simp only [dotProduct, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    ofFn_eq_sum_monomial, Finset.sum_mul, coeff_add, finsetSum_coeff]
  congr 1 <;> refine Finset.sum_congr rfl fun l _ => ?_ <;>
    rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, mul_comm]

/-- The matrix acts on a coefficient vector as two polynomial multipliers. -/
theorem subresultantMatrix_mulVec [CommSemiring R] [DecidableEq R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (j : ℕ) (v : Fin ((m - j) + (n - j)) → R)
    (i : Fin ((m - j) + (n - j))) :
    (subresultantMatrix p q m n j).mulVec v i =
      (ofFn (m - j) (fun k => v (Fin.castAdd (n - j) k)) * q +
        ofFn (n - j) (fun k => v (Fin.natAdd (m - j) k)) * p).coeff
          (i.val + j) :=
  coefficientRow_dotProduct hm hn (m - j) (n - j) (i.val + j) v

/-- Swapping inputs exchanges the two column blocks. -/
theorem subresultantMatrix_comm [Semiring R] (p q : R[X]) (m n j : ℕ) :
    subresultantMatrix p q m n j =
      (subresultantMatrix q p n m j).reindex
        (finCongr (add_comm (n - j) (m - j))) finAddFlip := by
  ext i k
  induction k using Fin.addCases <;> simp [subresultantMatrix, finAddFlip]

/-- The sign of an iterated permutation is the corresponding power of its sign. -/
private lemma sign_pow {N : ℕ} (σ : Equiv.Perm (Fin N)) (k : ℕ) :
    Equiv.Perm.sign (σ ^ k) = Equiv.Perm.sign σ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.sign_mul, ih, pow_succ]

/-- The block-swap sign is `(-1) ^ (m * n)`. -/
theorem sign_finAddFlip_trans_finCongr (m n : ℕ) :
    Equiv.Perm.sign (finAddFlip.trans (finCongr (add_comm n m))) =
      (-1) ^ (m * n) := by
  by_cases hm : m = 0
  · subst m
    have hid : finAddFlip.trans (finCongr (add_comm n 0)) = 1 := by
      apply Equiv.ext
      intro i
      have hi : i = Fin.natAdd 0 (Fin.cast (Nat.zero_add n) i) := by
        ext
        simp
      rw [hi, Equiv.trans_apply, finAddFlip_apply_natAdd]
      apply Fin.ext
      simp [finCongr]
    rw [hid]
    simp
  by_cases hn : n = 0
  · subst n
    have hid : finAddFlip.trans (finCongr (add_comm 0 m)) = 1 := by
      apply Equiv.ext
      intro i
      have hi : i = Fin.castAdd 0 (Fin.cast (Nat.add_zero m) i) := by
        ext
        simp
      rw [hi, Equiv.trans_apply, finAddFlip_apply_castAdd]
      apply Fin.ext
      simp [finCongr]
    rw [hid]
    simp
  let k : Fin (m + n) := ⟨n, by omega⟩
  have hperm : finAddFlip.trans (finCongr (add_comm n m)) = finCycle k := by
    apply Equiv.ext
    intro i
    cases i using Fin.addCases with
    | left i =>
      rw [Equiv.trans_apply, finAddFlip_apply_castAdd]
      apply Fin.ext
      simp only [finCongr_apply_coe, finCycle_apply, Fin.val_natAdd,
        Fin.val_castAdd, Fin.val_add, k]
      change n + i.val = (i.val + n) % (m + n)
      rw [Nat.add_comm n i.val]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    | right i =>
      rw [Equiv.trans_apply, finAddFlip_apply_natAdd]
      apply Fin.ext
      simp only [finCongr_apply_coe, finCycle_apply, Fin.val_castAdd,
        Fin.val_natAdd, Fin.val_add, k]
      rw [show m + i + n = (m + n) + i by omega]
      change i.val = (m + n + i.val) % (m + n)
      simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add]
      simpa only [Nat.mod_mod] using
        (Nat.mod_eq_of_lt (show i.val < m + n by omega)).symm
  have hcycleCoe : (finCycle k : Fin (m + n) → Fin (m + n)) =
      ⇑((finRotate (m + n)) ^ n) := by
    rw [← Equiv.Perm.iterate_eq_pow]
    exact finCycle_eq_finRotate_iterate
  have hcyclePerm : finCycle k = (finRotate (m + n)) ^ n := by
    apply Equiv.ext
    intro x
    exact congrFun hcycleCoe x
  rw [hperm, hcyclePerm, sign_pow, sign_finRotate, ← pow_mul]
  have hsplit : m + n - 1 = m + (n - 1) := by omega
  rw [hsplit, add_mul, Nat.mul_comm (n - 1) n, pow_add,
    Even.neg_one_pow (Nat.even_mul_pred_self n), mul_one]

/-- The fixed-bound principal subresultant coefficient. -/
noncomputable def psc [CommRing R] (p q : R[X]) (m n j : ℕ) : R :=
  (subresultantMatrix p q m n j).det

/-- The PSC is the determinant of its matrix. -/
theorem psc_def [CommRing R] (p q : R[X]) (m n j : ℕ) :
    psc p q m n j = (subresultantMatrix p q m n j).det := rfl

/-- The zeroth fixed-bound PSC is the fixed-bound resultant. -/
theorem psc_zero [CommRing R] (p q : R[X]) (m n : ℕ) :
    psc p q m n 0 = Polynomial.resultant p q m n := by
  rw [psc_def, subresultantMatrix_zero]
  rfl

/-- Fixed-bound PSCs commute with coefficient maps. -/
theorem psc_map_map [CommRing R] [CommRing S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    psc (p.map f) (q.map f) m n j = f (psc p q m n j) := by
  rw [psc_def, psc_def, subresultantMatrix_map_map, RingHom.map_det]

/-- At preserved actual degrees, fixed-bound mapping gives actual-degree mapping. -/
theorem psc_map_of_natDegree_eq [CommRing R] [CommRing S] (f : R →+* S)
    {p q : R[X]} (hp : (p.map f).natDegree = p.natDegree)
    (hq : (q.map f).natDegree = q.natDegree) (j : ℕ) :
    psc (p.map f) (q.map f) (p.map f).natDegree (q.map f).natDegree j =
      f (psc p q p.natDegree q.natDegree j) := by
  rw [hp, hq, psc_map_map]

/-- Swapping inputs changes the PSC by the Sylvester block-swap sign. -/
theorem psc_comm [CommRing R] (p q : R[X]) (m n j : ℕ) :
    psc p q m n j = (-1) ^ ((m - j) * (n - j)) * psc q p n m j := by
  rw [psc_def, psc_def, subresultantMatrix_comm, Matrix.det_reindex,
    finCongr_symm, sign_finAddFlip_trans_finCongr, mul_comm (n - j)]
  simp

/-- At the left formal degree bound the PSC is the corresponding coefficient power. -/
theorem psc_left_bound [CommRing R] (p q : R[X]) (m n : ℕ) :
    psc p q m n m = p.coeff m ^ (n - m) := by
  let M := subresultantMatrix p q m n m
  have htri : M.IsUpperTriangular := by
    intro i k hki
    induction k using Fin.addCases with
    | left k => exact Fin.elim0 (Fin.cast (by simp) k)
    | right k =>
      have hki' : (k : ℕ) < (i : ℕ) := by
        simpa only [id_eq, Fin.val_natAdd, Nat.sub_self, zero_add] using Fin.lt_def.mp hki
      simp only [M, subresultantMatrix, Matrix.of_apply, Fin.addCases_right]
      split_ifs with h
      · omega
      · rfl
  have hdiag (i : Fin ((m - m) + (n - m))) : M i i = p.coeff m := by
    induction i using Fin.addCases with
    | left i => exact Fin.elim0 (Fin.cast (by simp) i)
    | right i => simp [M, subresultantMatrix]
  rw [psc_def, Matrix.det_of_isUpperTriangular htri]
  simp_rw [hdiag]
  simp

/-- At the right formal degree bound the PSC is the corresponding coefficient power. -/
theorem psc_right_bound [CommRing R] (p q : R[X]) (m n : ℕ) :
    psc p q m n n = q.coeff n ^ (m - n) := by
  rw [psc_comm, psc_left_bound]
  simp

/-- At the terminal subresultant index the PSC is a power of the coefficient at the smaller
formal degree bound. -/
theorem psc_min [CommRing R] (p q : R[X]) (m n : ℕ) :
    psc p q m n (min m n) =
      if m ≤ n then p.coeff m ^ (n - m) else q.coeff n ^ (m - n) := by
  by_cases hmn : m ≤ n
  · rw [min_eq_left hmn, psc_left_bound]
    simp [hmn]
  · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
    rw [min_eq_right hnm, psc_right_bound]
    simp [hmn]

end Polynomial
