import Mathlib
import CAD.ProjectionDef
import Analysis.Delineability
import Algebra.ReductumNatDegree

namespace CollinsCAD

open Polynomial MvPolynomial

/-- Under leading-coefficient sign invariance, every polynomial is either
    identically zero on the base set or has an effective nonzero reductum whose
    leading coefficient is nowhere zero there. -/
theorem projection_effective_reductum {r : ℕ}
    (A : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (P : MvPolynomial (Fin (r + 1)) ℝ) (hP : P ∈ A)
    (S : Set (Fin r → ℝ)) (hS : SignInvariant (projL (reductaSet A)) S) :
    (∀ a ∈ S, fiberPoly r P a = 0) ∨
      ∃ k, reductum k (finLastEquiv ℝ r P) ≠ 0 ∧
        (∀ a ∈ S, fiberPoly r P a =
          (reductum k (finLastEquiv ℝ r P)).map (MvPolynomial.eval a)) ∧
        (∀ a ∈ S, MvPolynomial.eval a
          (reductum k (finLastEquiv ℝ r P)).leadingCoeff ≠ 0) := by
  classical
  let q := finLastEquiv ℝ r P
  have hmem (k : ℕ) (hk : k ≤ q.support.card) (hne : reductum k q ≠ 0) :
      reductum k q ∈ reductaSet A := by
    apply mem_reductaSet.mpr
    exact ⟨P, hP, k, hk, hne, rfl⟩
  have hlc_mem (k : ℕ) (hk : k ≤ q.support.card) (hne : reductum k q ≠ 0) :
      (reductum k q).leadingCoeff ∈ projL (reductaSet A) := by
    apply mem_projL.mpr
    exact ⟨reductum k q, hmem k hk hne, rfl⟩
  by_cases hex : ∃ k ≤ q.support.card, ∃ a ∈ S,
      MvPolynomial.eval a (reductum k q).leadingCoeff ≠ 0
  · right
    let k := Nat.find hex
    have hk_spec := Nat.find_spec hex
    rcases hk_spec with ⟨hk, a0, ha0, hne0⟩
    have hB0 : reductum k q ≠ 0 := by
      intro hz
      dsimp [k] at hz
      apply hne0
      simp [hz]
    have hearlier : ∀ i < k, ∀ a ∈ S,
        MvPolynomial.eval a (reductum i q).leadingCoeff = 0 := by
      intro i hi a ha
      by_contra hne
      have hi_le : i ≤ q.support.card := le_trans (Nat.le_of_lt hi) hk
      exact Nat.find_min hex hi ⟨hi_le, a, ha, hne⟩
    have hbridge : ∀ a ∈ S, fiberPoly r P a =
        (reductum k q).map (MvPolynomial.eval a) := by
      intro a ha
      simpa [q] using fiberPoly_eq_reductum_map_of_leadingCoeff_eq_zero P a
        (fun i hi => hearlier i hi a ha)
    have hsign : SignInvariantPoly (reductum k q).leadingCoeff S :=
      hS _ (hlc_mem k hk hB0)
    have hlc_ne : ∀ a ∈ S,
        MvPolynomial.eval a (reductum k q).leadingCoeff ≠ 0 := by
      intro a ha
      rcases SignInvariantPoly.eq_or_pos_or_neg hsign with hzero | hpos | hneg
      · exact (hne0 (hzero a0 ha0)).elim
      · exact ne_of_gt (hpos a ha)
      · exact ne_of_lt (hneg a ha)
    exact ⟨k, hB0, hbridge, hlc_ne⟩
  · left
    intro a ha
    have hall : ∀ i < q.support.card + 1,
        MvPolynomial.eval a (reductum i q).leadingCoeff = 0 := by
      intro i hi
      by_cases hz : reductum i q = 0
      · simp [hz]
      · by_contra hne
        exact hex ⟨i, by omega, a, ha, hne⟩
    have hbridge := fiberPoly_eq_reductum_map_of_leadingCoeff_eq_zero P a hall
    rw [reductum_eq_zero_of_support_card_le q (Nat.le_succ q.support.card)] at hbridge
    simpa [q] using hbridge

end CollinsCAD
