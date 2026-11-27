/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 as described in the file LICENSE.
Adapted for the Collins CAD demo; modified to use the local import structure.
-/

import Mathlib

/-!
# Polynomial coefficient windows

These helpers recover a polynomial from a bounded coefficient vector and turn a vanishing
coefficient window into a polynomial relation.  They are the degree-theoretic input to the
subresultant kernel argument.
-/

namespace Polynomial

variable {R S K : Type*}

/-- A polynomial of degree below `n` is recovered from its first `n` coefficients. -/
theorem ofFn_comp_toFn_eq_id_of_degree_lt [Semiring R] [DecidableEq R]
    {n : ℕ} {p : R[X]} (h : p.degree < n) :
    ofFn n (toFn n p) = p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · exact ofFn_comp_toFn_eq_id_of_natDegree_lt ((natDegree_lt_iff_degree_lt hp).mpr h)

/-- The product of a polynomial of degree below `a` with one of degree at most `n` has degree
below `a + n`; either factor may be zero. -/
theorem degree_mul_lt_of_degree_lt_of_natDegree_le [Semiring R] {A q : R[X]} {a n : ℕ}
    (hA : A.degree < a) (hq : q.natDegree ≤ n) :
    (A * q).degree < ((a + n : ℕ) : WithBot ℕ) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  · calc
      (A * q).degree ≤ A.degree + q.degree := degree_mul_le A q
      _ < (a : WithBot ℕ) + n :=
        WithBot.add_lt_add_of_lt_of_le (degree_ne_bot.mpr hq0) hA (degree_le_of_natDegree_le hq)
      _ = ((a + n : ℕ) : WithBot ℕ) := by push_cast; rfl

/-- A relation with multipliers below the two formal degree windows has degree below the end of
the combined coefficient window. -/
theorem degree_mul_add_mul_lt_of_degree_lt_of_natDegree_le
    [Semiring R] {p q A B : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hA : A.degree < (m - j : ℕ)) (hB : B.degree < (n - j : ℕ)) :
    (A * q + B * p).degree < (((m - j) + (n - j) + j : ℕ) : WithBot ℕ) := by
  apply (degree_add_le _ _).trans_lt
  apply max_lt
  · exact (degree_mul_lt_of_degree_lt_of_natDegree_le hA hn).trans_le
      (WithBot.coe_le_coe.mpr (by omega : m - j + n ≤ (m - j) + (n - j) + j))
  · exact (degree_mul_lt_of_degree_lt_of_natDegree_le hB hm).trans_le
      (WithBot.coe_le_coe.mpr (by omega : n - j + m ≤ (m - j) + (n - j) + j))

/-- Vanishing of the coefficient window above the degree of a common divisor forces the whole
polynomial relation to vanish. -/
theorem mul_add_mul_eq_zero_of_coeff_window [CommSemiring S] [NoZeroDivisors S]
    {p q A B g : S[X]} {m n : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hgp : g ∣ p) (hgq : g ∣ q)
    (hAdeg : A.degree < (m - g.natDegree : ℕ))
    (hBdeg : B.degree < (n - g.natDegree : ℕ))
    (hwin : ∀ i : Fin ((m - g.natDegree) + (n - g.natDegree)),
      (A * q + B * p).coeff (i + g.natDegree) = 0) :
    A * q + B * p = 0 := by
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [zero_dvd_iff] at hgp hgq
    simp [hgp, hgq]
  set d := g.natDegree
  have hsumdeg : (A * q + B * p).degree < ((m - d) + (n - d) + d : ℕ) :=
    degree_mul_add_mul_lt_of_degree_lt_of_natDegree_le hm hn hAdeg hBdeg
  have hdeg : (A * q + B * p).degree < d := by
    rw [degree_lt_iff_coeff_zero]
    intro e he
    by_cases hlt : e < (m - d) + (n - d) + d
    · have := hwin ⟨e - d, by omega⟩
      rwa [Nat.sub_add_cancel he] at this
    · apply coeff_eq_zero_of_degree_lt
      exact hsumdeg.trans_le (WithBot.coe_le_coe.mpr
        (by omega : (m - d) + (n - d) + d ≤ e))
  exact eq_zero_of_dvd_of_degree_lt
    (dvd_add (dvd_mul_of_dvd_right hgq _) (dvd_mul_of_dvd_right hgp _))
    (by rw [degree_eq_natDegree hg0]; exact hdeg)

/-- In a relation `A * q + B * p = 0`, a multiplier of degree below
`p.natDegree - gcd(p,q).natDegree` must vanish. -/
theorem eq_zero_of_mul_add_mul_eq_zero_of_degree_lt [Field K] [DecidableEq K]
    {p q A B : K[X]} (hAB : A * q + B * p = 0)
    (hA : A.degree < ((p.natDegree - (EuclideanDomain.gcd p q).natDegree : ℕ) : WithBot ℕ)) :
    A = 0 := by
  by_contra hA0
  have hlt := (natDegree_lt_iff_degree_lt hA0).mpr hA
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hlt
  have hg : EuclideanDomain.gcd p q ≠ 0 :=
    fun h => hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hdvd : p ∣ A * EuclideanDomain.gcd p q :=
    ⟨A * EuclideanDomain.gcdA p q - B * EuclideanDomain.gcdB p q, by
      rw [EuclideanDomain.gcd_eq_gcd_ab]
      linear_combination EuclideanDomain.gcdB p q * hAB⟩
  have := (natDegree_le_of_dvd hdvd (mul_ne_zero hA0 hg)).trans natDegree_mul_le
  omega

end Polynomial
