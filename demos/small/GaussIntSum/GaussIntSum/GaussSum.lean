import Mathlib

/-!
# Gauss summation identity

Proves `1 + 2 + ⋯ + n = n * (n + 1) / 2` for the first `n` positive
integers.
-/

/-- The sum of the first `n` positive integers, computed recursively. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

/-- **Gauss's identity**: `1 + 2 + ⋯ + n = n * (n + 1) / 2`. -/
theorem gauss_sum_identity (n : ℕ) : sumTo n = n * (n + 1) / 2 := by
  have key : 2 * sumTo n = n * (n + 1) := by
    induction n with
    | zero => rfl
    | succ k ih =>
      show 2 * ((k + 1) + sumTo k) = (k + 1) * ((k + 1) + 1)
      rw [Nat.mul_add, ih]
      ring
  calc
    sumTo n = 2 * sumTo n / 2 :=
      (Nat.mul_div_cancel_left (m := sumTo n) (n := 2) (by omega)).symm
    _ = n * (n + 1) / 2 := by rw [key]
