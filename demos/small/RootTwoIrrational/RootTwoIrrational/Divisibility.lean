import Mathlib

/-!
# Divisibility helpers

Small lemmas about primes and divisibility used by the other files in this
module.
-/

/-- Any prime is strictly greater than one. -/
theorem prime_gt_one (p : ℕ) (hp : Nat.Prime p) : 1 < p :=
  hp.one_lt

/-- If a prime divides a product of two equal factors, it divides the base. -/
theorem prime_dvd_square (p a : ℕ) (hp : Nat.Prime p) (h : p ∣ a * a) : p ∣ a :=
  (hp.dvd_mul.1 h).elim id id
