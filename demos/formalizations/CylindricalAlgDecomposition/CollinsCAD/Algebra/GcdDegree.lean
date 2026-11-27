/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 as described in the file LICENSE.
Adapted for the Collins CAD demo; modified to use the local import structure.
-/

import Mathlib
import Algebra.Subresultant
import Algebra.GcdPsc

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

/-- At the gcd degree, the actual-degree PSC is nonzero whenever the left input is nonzero. -/
theorem psc_ne_zero_of_natDegree_gcd {K : Type*} [Field K] [DecidableEq K]
    (A B : Polynomial K) (hA0 : A ≠ 0) :
    psc A B (EuclideanDomain.gcd A B).natDegree ≠ 0 := by
  rw [psc_eq_fixed_psc]
  exact mul_ne_zero
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Polynomial.psc_natDegree_gcd_ne_zero hA0 rfl le_rfl)

/-- Below the gcd degree, the actual-degree PSC vanishes. -/
theorem psc_eq_zero_of_lt_natDegree_gcd {K : Type*} [Field K] [DecidableEq K]
    (A B : Polynomial K) (j : ℕ)
    (hj : j < (EuclideanDomain.gcd A B).natDegree) :
    psc A B j = 0 := by
  rw [psc_eq_fixed_psc,
    Polynomial.psc_eq_zero_of_lt_natDegree_gcd le_rfl le_rfl hj, mul_zero]

/-- The unified subresultant gcd criterion at actual degrees. -/
theorem natDegree_gcd_eq_iff_psc {K : Type*} [Field K] [DecidableEq K]
    (A B : Polynomial K) (j : ℕ) :
    (EuclideanDomain.gcd A B).natDegree = j ↔
      psc A B j ≠ 0 ∧ ∀ i < j, psc A B i = 0 := by
  have hfixed_iff (i : ℕ) : psc A B i = 0 ↔
      Polynomial.psc A B A.natDegree B.natDegree i = 0 := by
    rw [psc_eq_fixed_psc, mul_eq_zero]
    have hs : (-1 : K) ^ ((A.natDegree - i) * (B.natDegree - i)) ≠ 0 :=
      pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    simp [hs]
  constructor
  · intro h
    have hf := (Polynomial.natDegree_gcd_eq_iff_psc A B j).mp h
    refine ⟨?_, ?_⟩
    · intro hz
      exact hf.1 ((hfixed_iff j).mp hz)
    · intro i hi
      exact (hfixed_iff i).mpr (hf.2 i hi)
  · rintro ⟨hj, hlt⟩
    apply (Polynomial.natDegree_gcd_eq_iff_psc A B j).mpr
    refine ⟨?_, ?_⟩
    · intro hz
      exact hj ((hfixed_iff j).mpr hz)
    · intro i hi
      exact (hfixed_iff i).mp (hlt i hi)

/-- Equality of actual-degree PSC zero patterns up to the smaller degree determines equality
of gcd degrees, including for polynomial pairs over different fields. -/
theorem natDegree_gcd_eq_of_psc_eq_zero_iff {K L : Type*} [Field K] [Field L]
    [DecidableEq K] [DecidableEq L] {A B : Polynomial K} {A' B' : Polynomial L}
    (hA'0 : A' ≠ 0) (hB'0 : B' ≠ 0)
    (h : ∀ j ≤ min A'.natDegree B'.natDegree, psc A B j = 0 ↔ psc A' B' j = 0) :
    (EuclideanDomain.gcd A B).natDegree = (EuclideanDomain.gcd A' B').natDegree := by
  set d := (EuclideanDomain.gcd A' B').natDegree
  have hd : d ≤ min A'.natDegree B'.natDegree :=
    le_min (Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left A' B') hA'0)
      (Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right A' B') hB'0)
  obtain ⟨hne, hlt⟩ := (natDegree_gcd_eq_iff_psc A' B' d).1 rfl
  exact (natDegree_gcd_eq_iff_psc A B d).2
    ⟨fun h0 => hne ((h d hd).1 h0), fun i hi => (h i (hi.le.trans hd)).2 (hlt i hi)⟩

/-- At the index equal to $\deg\gcd(A,B)$, the principal subresultant coefficient is nonzero. -/
theorem psc_ne_zero_of_gcd_eq {K : Type*} [Field K] [DecidableEq K]
    (A B : Polynomial K) (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hjA : (EuclideanDomain.gcd A B).natDegree ≤ A.natDegree)
    (hjB : (EuclideanDomain.gcd A B).natDegree ≤ B.natDegree)
    (hj : (EuclideanDomain.gcd A B).natDegree = j) :
    psc A B j ≠ 0 := by
  have _hB0 := hB0
  have _hjA := hjA
  have _hjB := hjB
  simpa [hj] using psc_ne_zero_of_natDegree_gcd A B hA0

end CollinsCAD
