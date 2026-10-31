import Divisibility
import EuclidLemma

/-!
# Irrationality of √2

The classic proof by contradiction: if `a * a = 2 * (b * b)` with `b ≠ 0`,
then the prime `2` divides `a` (so it divides `b` too, by `euclid_lemma`),
yielding an infinite descent.
-/

/-- **√2 is irrational**: there are no natural numbers `a` and `b`, with
`b ≠ 0`, such that `a * a = 2 * (b * b)`. -/
theorem sqrt_two_irrational :
    ¬ ∃ a b : ℕ, b ≠ 0 ∧ a * a = 2 * (b * b) := by
  sorry
