import Mathlib
import Algebra.EvalLastComm

namespace CollinsCAD

open Polynomial MvPolynomial

/-!
## Sign invariance and delineability

This file supplies the topological predicates used throughout the cylindrical
algebraic decomposition: sign-invariance of a finite set of polynomials on a
set `S`, and Collins' notion of (real) delineability of the roots of a
polynomial in its last variable.
-/

/-- The polynomial obtained by substituting the first $r$ coordinates of a
    point $a$ into $P$ and viewing the result as a univariate polynomial in the
    last coordinate. -/
noncomputable def fiberPoly (r : ℕ) (P : MvPolynomial (Fin (r + 1)) ℝ)
    (a : Fin r → ℝ) : Polynomial ℝ :=
  (finLastEquiv ℝ r P).map (MvPolynomial.eval a)

/-- Evaluating the fibre polynomial at $x$ agrees with evaluating $P$ at the
    tuple obtained by appending $x$ to $a$. -/
theorem fiberPoly_eval (r : ℕ) (P : MvPolynomial (Fin (r + 1)) ℝ)
    (a : Fin r → ℝ) (x : ℝ) :
    Polynomial.eval x (fiberPoly r P a) = MvPolynomial.eval (Fin.snoc a x) P := by
  rw [fiberPoly, eval_last_comm]

/-- A polynomial is sign-invariant on $S$ if $\operatorname{sign}(P(a))$ is the
    same for every $a \in S$. -/
def SignInvariantPoly (P : MvPolynomial (Fin r) ℝ) (S : Set (Fin r → ℝ)) : Prop :=
  ∃ s : SignType, ∀ a ∈ S, SignType.sign (MvPolynomial.eval a P) = s

/-- A finite set of polynomials is sign-invariant on $S$ when each of its
    elements is. -/
def SignInvariant (A : Finset (MvPolynomial (Fin r) ℝ)) (S : Set (Fin r → ℝ)) : Prop :=
  ∀ P ∈ A, SignInvariantPoly P S

/-- A sign-invariant polynomial is everywhere zero, everywhere positive, or
    everywhere negative on $S$. -/
theorem SignInvariantPoly.eq_or_pos_or_neg {P : MvPolynomial (Fin r) ℝ}
    {S : Set (Fin r → ℝ)} (h : SignInvariantPoly P S) :
    (∀ a ∈ S, MvPolynomial.eval a P = 0) ∨
      (∀ a ∈ S, 0 < MvPolynomial.eval a P) ∨
      (∀ a ∈ S, MvPolynomial.eval a P < 0) := by
  rcases h with ⟨s, hs⟩
  rcases SignType.trichotomy s with hsneg | hszero | hspos
  · right; right
    intro a ha
    have hsign := hs a ha
    rw [hsneg] at hsign
    exact (sign_eq_neg_one_iff).mp hsign
  · left
    intro a ha
    have hsign := hs a ha
    rw [hszero] at hsign
    exact (sign_eq_zero_iff).mp hsign
  · right; left
    intro a ha
    have hsign := hs a ha
    rw [hspos] at hsign
    exact (sign_eq_one_iff).mp hsign

/-- A polynomial that does not vanish anywhere on a connected set is
    sign-invariant there: the intermediate value theorem forces its sign to be
    constant. -/
theorem SignInvariantPoly.of_connected_ne_zero {P : MvPolynomial (Fin r) ℝ}
    {S : Set (Fin r → ℝ)} (hS : IsConnected S)
    (hne : ∀ a ∈ S, MvPolynomial.eval a P ≠ 0) : SignInvariantPoly P S := by
  classical
  rcases hS.nonempty with ⟨a0, ha0⟩
  refine ⟨SignType.sign (MvPolynomial.eval a0 P), ?_⟩
  intro a ha
  let f : (Fin r → ℝ) → ℝ := fun x => MvPolynomial.eval x P
  have hfcont : Continuous f := MvPolynomial.continuous_eval P
  by_cases hpos0 : 0 < f a0
  · have hpos : 0 < f a := by
      by_contra hnpos
      have hle : f a ≤ 0 := le_of_not_gt hnpos
      have hzero : (0 : ℝ) ∈ f '' S :=
        hS.isPreconnected.intermediate_value ha ha0 hfcont.continuousOn
          (by exact ⟨hle, le_of_lt hpos0⟩)
      rcases hzero with ⟨x, hxS, hx0⟩
      exact hne x hxS hx0
    have hs0 : SignType.sign (f a0) = 1 := (sign_eq_one_iff).mpr hpos0
    have hs : SignType.sign (f a) = 1 := (sign_eq_one_iff).mpr hpos
    simpa [f, hs0, hs]
  · have hneg0 : f a0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos0) (hne a0 ha0)
    have hneg : f a < 0 := by
      by_contra hnneg
      have hge : 0 ≤ f a := le_of_not_gt hnneg
      have hzero : (0 : ℝ) ∈ f '' S :=
        hS.isPreconnected.intermediate_value ha0 ha hfcont.continuousOn
          (by exact ⟨le_of_lt hneg0, hge⟩)
      rcases hzero with ⟨x, hxS, hx0⟩
      exact hne x hxS hx0
    have hs0 : SignType.sign (f a0) = -1 := (sign_eq_neg_one_iff).mpr hneg0
    have hs : SignType.sign (f a) = -1 := (sign_eq_neg_one_iff).mpr hneg
    simpa [f, hs0, hs]

/-- A finite strictly ordered family of continuous functions $f_i$ delineates
    the real roots of $P$ on $S$ if each $f_i(a)$ is a root of the fibre
    polynomial of $P$ at $a$, with a constant positive multiplicity $e_i$, the
    $f_i(a)$ are strictly increasing, and every real root of the fibre occurs
    among them. -/
def IsRealDelineable (P : MvPolynomial (Fin (r + 1)) ℝ) (S : Set (Fin r → ℝ)) : Prop :=
  ∃ (k : ℕ) (f : Fin k → (Fin r → ℝ) → ℝ) (e : Fin k → ℕ),
    (∀ i, ContinuousOn (f i) S) ∧
    (∀ i a, a ∈ S → 0 < e i ∧
      Polynomial.eval (f i a) (fiberPoly r P a) = 0 ∧
      Polynomial.rootMultiplicity (f i a) (fiberPoly r P a) = e i) ∧
    (∀ a ∈ S, ∀ x : ℝ, Polynomial.eval x (fiberPoly r P a) = 0 → ∃ i, f i a = x) ∧
    (∀ (i j : Fin k) (a : Fin r → ℝ), a ∈ S → i < j → f i a < f j a)

/-- The full complex analogue of delineability: a strictly ordered family of
    continuous real root functions together with a family of continuous
    non-real root functions, exhausting all complex roots with constant
    multiplicities. -/
def IsDelineable (P : MvPolynomial (Fin (r + 1)) ℝ) (S : Set (Fin r → ℝ)) : Prop :=
  ∃ (k l : ℕ) (fr : Fin k → (Fin r → ℝ) → ℝ) (fc : Fin l → (Fin r → ℝ) → ℂ)
      (er : Fin k → ℕ) (ec : Fin l → ℕ),
    (∀ i, ContinuousOn (fr i) S) ∧
    (∀ i, ContinuousOn (fc i) S) ∧
    (∀ i a, a ∈ S → 0 < er i ∧
      Polynomial.eval ((fr i a : ℝ) : ℂ) ((fiberPoly r P a).map (algebraMap ℝ ℂ)) = 0 ∧
      Polynomial.rootMultiplicity ((fr i a : ℝ) : ℂ)
        ((fiberPoly r P a).map (algebraMap ℝ ℂ)) = er i) ∧
    (∀ i a, a ∈ S → 0 < ec i ∧
      Polynomial.eval (fc i a) ((fiberPoly r P a).map (algebraMap ℝ ℂ)) = 0 ∧
      Polynomial.rootMultiplicity (fc i a)
        ((fiberPoly r P a).map (algebraMap ℝ ℂ)) = ec i ∧ (fc i a).im ≠ 0) ∧
    (∀ a ∈ S, ∀ z : ℂ,
      Polynomial.eval z ((fiberPoly r P a).map (algebraMap ℝ ℂ)) = 0 →
        (∃ i, (fr i a : ℂ) = z) ∨ (∃ i, fc i a = z)) ∧
    (∀ (i j : Fin k) (a : Fin r → ℝ), a ∈ S → i < j → fr i a < fr j a)

end CollinsCAD
