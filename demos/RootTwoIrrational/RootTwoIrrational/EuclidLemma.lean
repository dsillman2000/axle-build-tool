import Divisibility

/-!
# Euclid's lemma

If a prime divides a product of two numbers, it divides at least one of
the factors.
-/

/-- **Euclid's lemma**: a prime dividing `a * b` divides `a` or `b`. -/
theorem euclid_lemma (p a b : ℕ) (hp : Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  sorry
