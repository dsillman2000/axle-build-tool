import Mathlib
import Divisibility
import EuclidLemma

/-!
# Irrationality of √2

The classic proof by infinite descent: if `a * a = 2 * (b * b)` with
`b ≠ 0`, then `2` divides `a` (so `a = 2 * c` and `b * b = 2 * (c * c)`
with `0 < c < a`), and strong induction on `a` closes the descent.
-/

/-- **√2 is irrational**: there are no natural numbers `a` and `b`, with
`b ≠ 0`, such that `a * a = 2 * (b * b)`. -/
theorem sqrt_two_irrational :
    ¬ ∃ a b : ℕ, b ≠ 0 ∧ a * a = 2 * (b * b) := by
  have aux : ∀ a b : ℕ, b ≠ 0 → a * a = 2 * (b * b) → False := by
    intro a
    induction a using Nat.strongRecOn with
    | ind a ih =>
      intro b hb ha
      have hbb_pos : 0 < b * b := by positivity
      have hpa : 0 < a := by
        by_cases h0 : 0 < a
        · exact h0
        · have ha0 : a = 0 := by omega
          rw [ha0, Nat.zero_mul] at ha
          omega
      have h2a : 2 ∣ a :=
        prime_dvd_square 2 a (by decide) (⟨b * b, ha⟩ : 2 ∣ a * a)
      obtain ⟨c, hc⟩ := h2a
      have hpc : 0 < c := by
        by_cases h0 : 0 < c
        · exact h0
        · have hc0 : c = 0 := by omega
          rw [hc, hc0, Nat.mul_zero] at hpa
          omega
      have hnc : c ≠ 0 := by
        intro h0
        rw [hc, h0] at hpa
        omega
      have hba : b < a := by
        by_cases h : b < a
        · exact h
        · have hle : a ≤ b := Nat.le_of_not_lt h
          have hle2 : a * a ≤ b * b := Nat.mul_le_mul hle hle
          omega
      have hbb : b * b = 2 * (c * c) := by
        rw [hc] at ha
        rw [Nat.mul_mul_mul_comm] at ha
        have h4 : 4 * (c * c) = 2 * (b * b) := ha
        omega
      exact ih b hba c hnc hbb
  intro ⟨a, b, hb, ha⟩
  exact aux a b hb ha
