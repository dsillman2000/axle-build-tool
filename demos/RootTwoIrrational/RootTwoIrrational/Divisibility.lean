/-!
# Divisibility helpers

Small lemmas about primes and divisibility used by the other files in this
module. Written against core Lean 4 only — no external dependencies.
-/

/-- A minimal primality predicate: `p` is prime if it is at least `2` and
its only divisors are `1` and `p` itself. -/
def Prime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p

/-- Any prime is strictly greater than one. -/
theorem prime_gt_one (p : ℕ) (hp : Prime p) : 1 < p := by
  sorry

/-- If a prime divides a product of two equal factors, it divides the base. -/
theorem prime_dvd_square (p a : ℕ) (hp : Prime p) (h : p ∣ a * a) : p ∣ a := by
  sorry
