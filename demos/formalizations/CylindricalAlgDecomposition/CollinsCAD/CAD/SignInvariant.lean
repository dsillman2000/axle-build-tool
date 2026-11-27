import Mathlib
import Analysis.Delineability
import CAD.ProjectionDef

namespace CollinsCAD

/-- Sign invariance is inherited by subsets of the projected polynomial set. -/
theorem SignInvariant.mono {r : ℕ} {A B : Finset (MvPolynomial (Fin r) ℝ)}
    {S : Set (Fin r → ℝ)} (h : SignInvariant B S) (hsub : A ⊆ B) :
    SignInvariant A S := by
  intro P hP
  exact h P (hsub hP)

/-- A polynomial that vanishes everywhere is sign-invariant with sign zero. -/
theorem SignInvariantPoly.of_eq_zero {r : ℕ}
    {P : MvPolynomial (Fin r) ℝ} {S : Set (Fin r → ℝ)}
    (h : ∀ a ∈ S, MvPolynomial.eval a P = 0) : SignInvariantPoly P S := by
  refine ⟨0, ?_⟩
  intro a ha
  simp [h a ha]

/-- A sign-invariant polynomial that vanishes at one point vanishes everywhere. -/
theorem SignInvariantPoly.eq_zero_of_eq_zero {r : ℕ}
    {P : MvPolynomial (Fin r) ℝ} {S : Set (Fin r → ℝ)}
    (h : SignInvariantPoly P S) {a₀ : Fin r → ℝ} (ha₀ : a₀ ∈ S)
    (h0 : MvPolynomial.eval a₀ P = 0) : ∀ a ∈ S, MvPolynomial.eval a P = 0 := by
  rcases SignInvariantPoly.eq_or_pos_or_neg h with hz | hpos | hneg
  · exact hz
  · exact (lt_irrefl 0 (by simpa [h0] using hpos a₀ ha₀)).elim
  · exact (lt_irrefl 0 (by simpa [h0] using hneg a₀ ha₀)).elim

/-- A sign-invariant polynomial that is nonzero at one point is nonzero
    everywhere. -/
theorem SignInvariantPoly.ne_zero_of_ne_zero {r : ℕ}
    {P : MvPolynomial (Fin r) ℝ} {S : Set (Fin r → ℝ)}
    (h : SignInvariantPoly P S) {a₀ : Fin r → ℝ} (ha₀ : a₀ ∈ S)
    (h0 : MvPolynomial.eval a₀ P ≠ 0) : ∀ a ∈ S, MvPolynomial.eval a P ≠ 0 := by
  rcases SignInvariantPoly.eq_or_pos_or_neg h with hz | hpos | hneg
  · exact (h0 (hz a₀ ha₀)).elim
  · intro a ha
    exact ne_of_gt (hpos a ha)
  · intro a ha
    exact ne_of_lt (hneg a ha)

/-- Full projection sign invariance restricts to leading coefficients. -/
theorem signInvariant_projL_of_collinsProj {r : ℕ}
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} {S : Set (Fin r → ℝ)}
    (h : SignInvariant (collinsProj A) S) :
    SignInvariant (projL (reductaSet A)) S := by
  intro Q hQ
  exact h Q (mem_collinsProj.mpr (Or.inl hQ))

/-- Full projection sign invariance restricts to derivative PSCs. -/
theorem signInvariant_projS1_of_collinsProj {r : ℕ}
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} {S : Set (Fin r → ℝ)}
    (h : SignInvariant (collinsProj A) S) :
    SignInvariant (projS1 (reductaSet A)) S := by
  intro Q hQ
  exact h Q (mem_collinsProj.mpr (Or.inr (Or.inl hQ)))

/-- Full projection sign invariance restricts to pairwise PSCs. -/
theorem signInvariant_projS2_of_collinsProj {r : ℕ}
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} {S : Set (Fin r → ℝ)}
    (h : SignInvariant (collinsProj A) S) :
    SignInvariant (projS2 (reductaSet A)) S := by
  intro Q hQ
  exact h Q (mem_collinsProj.mpr (Or.inr (Or.inr hQ)))

end CollinsCAD
