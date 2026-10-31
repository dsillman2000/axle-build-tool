import Mathlib
import Divisibility

/-!
# Euclid's lemma

If a prime divides a product of two numbers, it divides at least one of
the factors.
-/

/-- **Euclid's lemma**: a prime dividing `a * b` divides `a` or `b`. -/
theorem euclid_lemma (p a b : ℕ) (hp : Nat.Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b :=
  hp.dvd_mul.1 h
