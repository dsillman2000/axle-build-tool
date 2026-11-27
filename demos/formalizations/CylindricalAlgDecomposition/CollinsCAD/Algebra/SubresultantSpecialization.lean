/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 as described in the file LICENSE.
Adapted for the Collins CAD demo; modified to use the local import structure.
-/

import Algebra.Subresultant
import Algebra.SubresultantDegreeDrop

/-!
# Actual-degree PSC specialization

These formulas account for degree drops after coefficient specialization.  A single degree drop
changes an actual-degree PSC by a nonzero scalar, while two strict degree drops force every PSC
below both specialized degrees to vanish.
-/

namespace CollinsCAD

open Polynomial

/-- Degree-preserving maps preserve the leading coefficient. -/
theorem leadingCoeff_map_of_natDegree_eq {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Polynomial R) (h : (A.map f).natDegree = A.natDegree) :
    (A.map f).leadingCoeff = f A.leadingCoeff := by
  change (A.map f).coeff (A.map f).natDegree = f (A.coeff A.natDegree)
  rw [h, Polynomial.coeff_map]

/-- If only the right degree drops, the evaluated actual-degree PSC is the specialized PSC up to
    the left leading-coefficient power and the block-swap sign. -/
theorem psc_map_of_right_degree_drop {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : Polynomial R) (j : ℕ)
    (hA : (A.map f).natDegree = A.natDegree)
    (hj : j ≤ min (A.map f).natDegree (B.map f).natDegree) :
    f (psc A B j) = (-1) ^ ((B.natDegree - (B.map f).natDegree) * (A.natDegree - j)) *
      f A.leadingCoeff ^ (B.natDegree - (B.map f).natDegree) *
        psc (A.map f) (B.map f) j := by
  have hBj : j ≤ (B.map f).natDegree := hj.trans (min_le_right _ _)
  have hAj : j ≤ A.natDegree := by simpa [hA] using hj.trans (min_le_left _ _)
  have hBN : (B.map f).natDegree ≤ B.natDegree := Polynomial.natDegree_map_le
  rw [psc_eq_fixed_psc, psc_eq_fixed_psc, map_mul, map_pow, map_neg, map_one,
    Polynomial.map_psc_of_right_degree_drop f (n := (B.map f).natDegree) (N := B.natDegree)
      le_rfl hBN hAj hBj]
  simp only [hA, Polynomial.leadingCoeff]
  have hb : ((B.map f).natDegree - j) +
      (B.natDegree - (B.map f).natDegree) = B.natDegree - j := by omega
  have hexp : (A.natDegree - j) * (B.natDegree - j) =
      (A.natDegree - j) * ((B.map f).natDegree - j) +
        (B.natDegree - (B.map f).natDegree) * (A.natDegree - j) := by
    calc
      (A.natDegree - j) * (B.natDegree - j) =
          (A.natDegree - j) * (((B.map f).natDegree - j) +
            (B.natDegree - (B.map f).natDegree)) := by rw [hb]
      _ = _ := by ring
  rw [hexp, pow_add]
  ring

/-- If only the left degree drops, the evaluated actual-degree PSC is the specialized PSC up to
    the right leading-coefficient power. -/
theorem psc_map_of_left_degree_drop {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : Polynomial R) (j : ℕ)
    (hB : (B.map f).natDegree = B.natDegree)
    (hj : j ≤ min (A.map f).natDegree (B.map f).natDegree) :
    f (psc A B j) = f B.leadingCoeff ^ (A.natDegree - (A.map f).natDegree) *
      psc (A.map f) (B.map f) j := by
  have hAj : j ≤ (A.map f).natDegree := hj.trans (min_le_left _ _)
  have hBj : j ≤ B.natDegree := by simpa [hB] using hj.trans (min_le_right _ _)
  have hAM : (A.map f).natDegree ≤ A.natDegree := Polynomial.natDegree_map_le
  rw [psc_eq_fixed_psc, psc_eq_fixed_psc, map_mul, map_pow, map_neg, map_one,
    Polynomial.map_psc_of_left_degree_drop f (m := (A.map f).natDegree) (M := A.natDegree)
      le_rfl hAM hAj hBj]
  simp only [hB, Polynomial.leadingCoeff]
  have ha : ((A.map f).natDegree - j) +
      (A.natDegree - (A.map f).natDegree) = A.natDegree - j := by omega
  have hexp : (A.natDegree - j) * (B.natDegree - j) =
      ((A.map f).natDegree - j) * (B.natDegree - j) +
        (A.natDegree - (A.map f).natDegree) * (B.natDegree - j) := by
    calc
      (A.natDegree - j) * (B.natDegree - j) =
          (((A.map f).natDegree - j) +
            (A.natDegree - (A.map f).natDegree)) * (B.natDegree - j) := by rw [ha]
      _ = _ := by ring
  rw [hexp, pow_add]
  have hdrop_sq : ((-1 : S) ^ ((A.natDegree - (A.map f).natDegree) * (B.natDegree - j))) *
      (-1 : S) ^ ((A.natDegree - (A.map f).natDegree) * (B.natDegree - j)) = 1 := by
    rw [← pow_add]
    have heven : (A.natDegree - (A.map f).natDegree) * (B.natDegree - j) +
        (A.natDegree - (A.map f).natDegree) * (B.natDegree - j) =
        2 * ((A.natDegree - (A.map f).natDegree) * (B.natDegree - j)) := by omega
    rw [heven, pow_mul]
    simp
  calc
    (-1 : S) ^ (((A.map f).natDegree - j) * (B.natDegree - j)) *
        (-1 : S) ^ ((A.natDegree - (A.map f).natDegree) * (B.natDegree - j)) *
      ((-1 : S) ^ ((A.natDegree - (A.map f).natDegree) * (B.natDegree - j)) *
        f (B.coeff B.natDegree) ^ (A.natDegree - (A.map f).natDegree) *
        Polynomial.psc (A.map f) (B.map f) (A.map f).natDegree B.natDegree j) =
      f (B.coeff B.natDegree) ^ (A.natDegree - (A.map f).natDegree) *
        ((-1 : S) ^ (((A.map f).natDegree - j) * (B.natDegree - j)) *
          Polynomial.psc (A.map f) (B.map f) (A.map f).natDegree B.natDegree j) *
        ((-1 : S) ^ ((A.natDegree - (A.map f).natDegree) * (B.natDegree - j)) *
          (-1 : S) ^ ((A.natDegree - (A.map f).natDegree) * (B.natDegree - j))) := by ring
    _ = _ := by rw [hdrop_sq, mul_one]

/-- If both specialized degrees drop strictly, every PSC below both specialized degrees maps to
    zero. -/
theorem psc_map_eq_zero_of_both_degree_drop {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : Polynomial R) (j : ℕ)
    (hA : (A.map f).natDegree < A.natDegree)
    (hB : (B.map f).natDegree < B.natDegree)
    (hj : j ≤ min (A.map f).natDegree (B.map f).natDegree) :
    f (psc A B j) = 0 := by
  have hj' : j < min A.natDegree B.natDegree := by omega
  rw [psc_eq_fixed_psc, map_mul, map_pow, map_neg, map_one,
    ← Polynomial.psc_map_map,
    Polynomial.psc_eq_zero_of_natDegree_lt_bounds hA hB hj', mul_zero]

/-- A nonzero evaluated PSC below both specialized degrees rules out a simultaneous degree
    drop. -/
theorem natDegree_map_eq_left_or_right_of_psc_map_ne_zero
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : Polynomial R) (j : ℕ)
    (hne : f (psc A B j) ≠ 0)
    (hj : j ≤ min (A.map f).natDegree (B.map f).natDegree) :
    (A.map f).natDegree = A.natDegree ∨ (B.map f).natDegree = B.natDegree := by
  by_contra h
  have hA : (A.map f).natDegree ≠ A.natDegree := fun ha => h (Or.inl ha)
  have hB : (B.map f).natDegree ≠ B.natDegree := fun hb => h (Or.inr hb)
  have hAlt : (A.map f).natDegree < A.natDegree :=
    lt_of_le_of_ne Polynomial.natDegree_map_le hA
  have hBlt : (B.map f).natDegree < B.natDegree :=
    lt_of_le_of_ne Polynomial.natDegree_map_le hB
  exact hne (psc_map_eq_zero_of_both_degree_drop f A B j hAlt hBlt hj)

/-- When at least one specialized degree is preserved and both fibres are nonzero, PSC
    zero/nonzero is transported across specialization. -/
theorem psc_map_eq_zero_iff_of_natDegree_eq_left_or_right
    {R S : Type*} [CommRing R] [Field S]
    (f : R →+* S) (A B : Polynomial R) (j : ℕ)
    (hA0 : A.map f ≠ 0) (hB0 : B.map f ≠ 0)
    (hdeg : (A.map f).natDegree = A.natDegree ∨
      (B.map f).natDegree = B.natDegree)
    (hj : j ≤ min (A.map f).natDegree (B.map f).natDegree) :
    f (psc A B j) = 0 ↔ psc (A.map f) (B.map f) j = 0 := by
  rcases hdeg with hA | hB
  · have hAlc : f A.leadingCoeff ≠ 0 := by
      rw [← leadingCoeff_map_of_natDegree_eq f A hA]
      exact Polynomial.leadingCoeff_ne_zero.mpr hA0
    have hsign : (-1 : S) ^ ((B.natDegree - (B.map f).natDegree) * (A.natDegree - j)) ≠ 0 :=
      pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    have hpow : f A.leadingCoeff ^ (B.natDegree - (B.map f).natDegree) ≠ 0 :=
      pow_ne_zero _ hAlc
    rw [psc_map_of_right_degree_drop f A B j hA hj]
    have hfactor := mul_ne_zero hsign hpow
    constructor
    · intro hz
      exact (mul_eq_zero.mp hz).resolve_left hfactor
    · intro hz
      rw [hz, mul_zero]
  · have hBlc : f B.leadingCoeff ≠ 0 := by
      rw [← leadingCoeff_map_of_natDegree_eq f B hB]
      exact Polynomial.leadingCoeff_ne_zero.mpr hB0
    have hpow : f B.leadingCoeff ^ (A.natDegree - (A.map f).natDegree) ≠ 0 :=
      pow_ne_zero _ hBlc
    rw [psc_map_of_left_degree_drop f A B j hB hj]
    constructor
    · intro hz
      exact (mul_eq_zero.mp hz).resolve_left hpow
    · intro hz
      rw [hz, mul_zero]

/-- Nonzero specialized PSCs preserve nonvanishing when one degree is preserved. -/
theorem psc_map_ne_zero_iff_of_natDegree_eq_left_or_right
    {R S : Type*} [CommRing R] [Field S]
    (f : R →+* S) (A B : Polynomial R) (j : ℕ)
    (hA0 : A.map f ≠ 0) (hB0 : B.map f ≠ 0)
    (hdeg : (A.map f).natDegree = A.natDegree ∨
      (B.map f).natDegree = B.natDegree)
    (hj : j ≤ min (A.map f).natDegree (B.map f).natDegree) :
    f (psc A B j) ≠ 0 ↔ psc (A.map f) (B.map f) j ≠ 0 := by
  exact not_congr (psc_map_eq_zero_iff_of_natDegree_eq_left_or_right
    f A B j hA0 hB0 hdeg hj)

end CollinsCAD
