/-!
# Gauss summation identity

Proves `1 + 2 + ⋯ + n = n * (n + 1) / 2` for the first `n` positive
integers. Written against core Lean 4 only — no external dependencies.
-/

/-- The sum of the first `n` positive integers, computed recursively. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

/-- **Gauss's identity**: `1 + 2 + ⋯ + n = n * (n + 1) / 2`. -/
theorem gauss_sum_identity (n : Nat) : sumTo n = n * (n + 1) / 2 := by
  sorry
