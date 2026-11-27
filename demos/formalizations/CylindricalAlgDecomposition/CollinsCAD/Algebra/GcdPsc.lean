/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 as described in the file LICENSE.
Adapted for the Collins CAD demo; modified to use the local import structure.
-/

import Algebra.FixedSubresultant
import Algebra.PolynomialDegreeWindow

/-!
# The subresultant gcd criterion

At fixed degree bounds, principal subresultant coefficients vanish below the gcd degree and are
nonzero at the gcd degree.  The proof reads the subresultant matrix directly as a polynomial
coefficient map and uses the gcd's Bézout identity to rule out a kernel vector at the terminal
index.
-/

namespace Polynomial

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A nontrivial relation `A * q + B * p = 0`, with multiplier degrees below the fixed-bound
windows, is a kernel vector, so the corresponding PSC vanishes. -/
theorem psc_eq_zero_of_mul_add_mul_eq_zero {p q A B : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hA : A.degree < (m - j : ℕ)) (hB : B.degree < (n - j : ℕ))
    (hAB : A * q + B * p = 0) (hne : A ≠ 0 ∨ B ≠ 0) :
    psc p q m n j = 0 := by
  classical
  rw [psc_def, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨Fin.append (toFn (m - j) A) (toFn (n - j) B), fun h0 => ?_, ?_⟩
  · have hA0 : toFn (m - j) A = 0 := _root_.funext fun k => by
      simpa using congrFun h0 (Fin.castAdd (n - j) k)
    have hB0 : toFn (n - j) B = 0 := _root_.funext fun k => by
      simpa using congrFun h0 (Fin.natAdd (m - j) k)
    rcases hne with hne | hne
    · exact hne (by rw [← ofFn_comp_toFn_eq_id_of_degree_lt hA, hA0, map_zero])
    · exact hne (by rw [← ofFn_comp_toFn_eq_id_of_degree_lt hB, hB0, map_zero])
  · funext i
    rw [subresultantMatrix_mulVec hm hn]
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
    rw [ofFn_comp_toFn_eq_id_of_degree_lt hA, ofFn_comp_toFn_eq_id_of_degree_lt hB,
      hAB, coeff_zero]

end Domain

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- Below the gcd degree, fixed-bound PSCs vanish whenever the bounds dominate the input degrees. -/
theorem psc_eq_zero_of_lt_natDegree_gcd {p q : K[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hj : j < (EuclideanDomain.gcd p q).natDegree) :
    psc p q m n j = 0 := by
  set g := EuclideanDomain.gcd p q
  have hg0 : g ≠ 0 := by
    rintro h
    rw [h, natDegree_zero] at hj
    exact absurd hj (Nat.not_lt_zero j)
  have hpg : g * (p / g) = p :=
    EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_left p q)
  have hqg : g * (q / g) = q :=
    EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_right p q)
  have hdeg : ∀ {r : K[X]} {k : ℕ}, r.natDegree ≤ k → g * (r / g) = r →
      (r / g).degree < (k - j : ℕ) := by
    intro r k hk hrg
    rcases eq_or_ne r 0 with rfl | hr
    · rw [EuclideanDomain.zero_div, degree_zero]
      exact WithBot.bot_lt_coe _
    · have hrg0 : r / g ≠ 0 := by
        rintro h
        rw [h, mul_zero] at hrg
        exact hr hrg.symm
      have := natDegree_mul hg0 hrg0
      rw [hrg] at this
      exact (natDegree_lt_iff_degree_lt hrg0).mp (by omega)
  refine psc_eq_zero_of_mul_add_mul_eq_zero (A := p / g) (B := -(q / g)) hm hn
    (hdeg hm hpg) (by rw [degree_neg]; exact hdeg hn hqg) ?_ ?_
  · rw [neg_mul, ← sub_eq_add_neg, sub_eq_zero]
    calc
      p / g * q = p / g * (g * (q / g)) := by rw [hqg]
      _ = q / g * (g * (p / g)) := by ring
      _ = q / g * p := by rw [hpg]
  · rcases eq_or_ne p 0 with rfl | hp
    · have hq : q ≠ 0 :=
        fun h => hg0 (EuclideanDomain.gcd_eq_zero_iff.mpr ⟨rfl, h⟩)
      refine Or.inr (neg_ne_zero.mpr fun h => hq ?_)
      rw [h, mul_zero] at hqg
      exact hqg.symm
    · refine Or.inl fun h => hp ?_
      rw [h, mul_zero] at hpg
      exact hpg.symm

/-- At the gcd degree the PSC is nonzero when the left bound is the actual degree of the
nonzero left polynomial and the right bound dominates the right polynomial. -/
theorem psc_natDegree_gcd_ne_zero {p q : K[X]} {m n : ℕ}
    (hp : p ≠ 0) (hm : p.natDegree = m) (hn : q.natDegree ≤ n) :
    psc p q m n (EuclideanDomain.gcd p q).natDegree ≠ 0 := by
  set g := EuclideanDomain.gcd p q with hg
  clear_value g
  have hgp : g ∣ p := hg ▸ EuclideanDomain.gcd_dvd_left p q
  have hgq : g ∣ q := hg ▸ EuclideanDomain.gcd_dvd_right p q
  set d := g.natDegree
  rw [psc_def, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv, hMv⟩
  have hwin (i : Fin ((m - d) + (n - d))) :
      (ofFn (m - d) (fun k => v (Fin.castAdd (n - d) k)) * q +
        ofFn (n - d) (fun k => v (Fin.natAdd (m - d) k)) * p).coeff (i + d) = 0 := by
    rw [← subresultantMatrix_mulVec hm.le hn, hMv, Pi.zero_apply]
  generalize hA : ofFn (m - d) (fun k => v (Fin.castAdd (n - d) k)) = A at hwin
  generalize hB : ofFn (n - d) (fun k => v (Fin.natAdd (m - d) k)) = B at hwin
  have hAdeg : A.degree < (m - d : ℕ) := hA ▸ ofFn_degree_lt _
  have hBdeg : B.degree < (n - d : ℕ) := hB ▸ ofFn_degree_lt _
  have hzero := mul_add_mul_eq_zero_of_coeff_window hm.le hn hgp hgq hAdeg hBdeg hwin
  have hA0 : A = 0 :=
    eq_zero_of_mul_add_mul_eq_zero_of_degree_lt hzero (by rw [hm, ← hg]; exact hAdeg)
  have hB0 : B = 0 := by
    rw [hA0, zero_mul, zero_add] at hzero
    exact (mul_eq_zero.mp hzero).resolve_right hp
  apply hv
  rw [hA0] at hA
  rw [hB0] at hB
  have h1 := injective_ofFn (m - d) (hA.trans (map_zero _).symm)
  have h2 := injective_ofFn (n - d) (hB.trans (map_zero _).symm)
  funext i
  induction i using Fin.addCases with
  | left k => exact congrFun h1 k
  | right k => exact congrFun h2 k

/-- At actual degrees, the gcd degree is the least index with nonzero PSC.  The zero-left-input
case is the empty terminal determinant. -/
theorem natDegree_gcd_eq_iff_psc (p q : K[X]) (j : ℕ) :
    (EuclideanDomain.gcd p q).natDegree = j ↔
      psc p q p.natDegree q.natDegree j ≠ 0 ∧
        ∀ i < j, psc p q p.natDegree q.natDegree i = 0 := by
  have hne : psc p q p.natDegree q.natDegree (EuclideanDomain.gcd p q).natDegree ≠ 0 := by
    rcases eq_or_ne p 0 with rfl | hp
    · rw [EuclideanDomain.gcd_zero_left, natDegree_zero, psc_right_bound,
        Nat.zero_sub, pow_zero]
      exact one_ne_zero
    · exact psc_natDegree_gcd_ne_zero hp rfl le_rfl
  constructor
  · rintro rfl
    exact ⟨hne, fun i hi => psc_eq_zero_of_lt_natDegree_gcd le_rfl le_rfl hi⟩
  · rintro ⟨hj, hlt⟩
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact hne (hlt _ h)
    · exact hj (psc_eq_zero_of_lt_natDegree_gcd le_rfl le_rfl h)

/-- Equality of PSC zero patterns up to the smaller actual degree determines equality of gcd
degrees, including for pairs over different fields. -/
theorem natDegree_gcd_eq_of_psc_eq_zero_iff {L : Type*} [Field L] [DecidableEq L]
    {p q : K[X]} {p' q' : L[X]} (hp' : p' ≠ 0) (hq' : q' ≠ 0)
    (h : ∀ j ≤ min p'.natDegree q'.natDegree,
      psc p q p.natDegree q.natDegree j = 0 ↔
        psc p' q' p'.natDegree q'.natDegree j = 0) :
    (EuclideanDomain.gcd p q).natDegree = (EuclideanDomain.gcd p' q').natDegree := by
  set d := (EuclideanDomain.gcd p' q').natDegree
  have hd : d ≤ min p'.natDegree q'.natDegree :=
    le_min (natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left p' q') hp')
      (natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right p' q') hq')
  obtain ⟨hne, hlt⟩ := (natDegree_gcd_eq_iff_psc p' q' d).1 rfl
  exact (natDegree_gcd_eq_iff_psc p q d).2
    ⟨fun h0 => hne ((h d hd).1 h0), fun i hi => (h i (hi.le.trans hd)).2 (hlt i hi)⟩

end Field

end Polynomial
