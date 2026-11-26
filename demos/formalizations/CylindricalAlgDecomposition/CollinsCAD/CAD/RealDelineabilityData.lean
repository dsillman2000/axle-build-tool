import Mathlib
import Analysis.Delineability
import CAD.Fiber
import CAD.Pairwise

namespace CollinsCAD

open Polynomial

/-- A packaged real-delineability witness. -/
structure RealDelineabilityData {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) ℝ) (S : Set (Fin r → ℝ)) where
  k : ℕ
  f : Fin k → (Fin r → ℝ) → ℝ
  e : Fin k → ℕ
  continuous : ∀ i, ContinuousOn (f i) S
  root_multiplicity : ∀ i a, a ∈ S → 0 < e i ∧
    Polynomial.eval (f i a) (fiberPoly r P a) = 0 ∧
    Polynomial.rootMultiplicity (f i a) (fiberPoly r P a) = e i
  exhaustive : ∀ a ∈ S, ∀ x : ℝ,
    Polynomial.eval x (fiberPoly r P a) = 0 → ∃ i, f i a = x
  strictMono : ∀ (i j : Fin k) (a : Fin r → ℝ),
    a ∈ S → i < j → f i a < f j a

/-- Any real-delineability witness can be packaged. -/
theorem IsRealDelineable.nonempty_data {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) ℝ} {S : Set (Fin r → ℝ)}
    (h : IsRealDelineable P S) : Nonempty (RealDelineabilityData P S) := by
  rcases h with ⟨k, f, e, hcont, hroot, hexhaust, hmono⟩
  exact ⟨⟨k, f, e, hcont, hroot, hexhaust, hmono⟩⟩

/-- Packaged data is a real-delineability witness. -/
theorem RealDelineabilityData.isRealDelineable {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) ℝ} {S : Set (Fin r → ℝ)}
    (W : RealDelineabilityData P S) : IsRealDelineable P S := by
  exact ⟨W.k, W.f, W.e, W.continuous, W.root_multiplicity, W.exhaustive, W.strictMono⟩

/-- Packaged data gives a continuous real root-branch family. -/
theorem RealDelineabilityData.branchFamily {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) ℝ} {S : Set (Fin r → ℝ)}
    (W : RealDelineabilityData P S) : IsRealRootBranchFamily P S W.f := by
  refine ⟨?_, W.continuous, ?_⟩
  · intro a ha
    exact fiberPoly_ne_zero_of_isRealDelineable
      (RealDelineabilityData.isRealDelineable W) a ha
  · intro i a ha
    exact (W.root_multiplicity i a ha).2.1

/-- Continuous branches that never meet preserve their basepoint order on a
    preconnected set. -/
theorem lt_of_continuous_ne_of_base_lt {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsPreconnected S) {a₀ : X} (ha₀ : a₀ ∈ S)
    {f g : X → ℝ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hne : ∀ a ∈ S, f a ≠ g a) (hbase : f a₀ < g a₀) :
    ∀ a ∈ S, f a < g a := by
  intro a ha
  by_contra hnot
  have hle : g a ≤ f a := le_of_not_gt hnot
  rcases hS.intermediate_value₂ ha₀ ha hf hg hbase.le hle with ⟨x, hxS, hx⟩
  exact hne x hxS hx

end CollinsCAD
