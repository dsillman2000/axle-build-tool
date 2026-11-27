import Mathlib
import Algebra.Reductum
import Algebra.FinLastEquiv
import Algebra.Subresultant
import Algebra.ReductumNatDegree

/-!
# Collins projection operators

The projection family consists of leading coefficients and principal
subresultant coefficients of the nonzero reducta of the input polynomials.
Nonzero constant reducta are retained because their leading coefficients
record the first nonzero last-variable coefficient on a base cell.
-/

namespace CollinsCAD

open Polynomial

variable {r : ℕ}

/-- All nonzero reducta of the last-variable view of `P`, including nonzero
    constant reducta. -/
noncomputable def reducta (P : MvPolynomial (Fin (r + 1)) ℝ) :
    Finset (Polynomial (MvPolynomial (Fin r) ℝ)) :=
  ((Finset.range ((finLastEquiv ℝ r P).support.card + 1)).image
    (fun k => reductum k (finLastEquiv ℝ r P))).filter (· ≠ 0)

/-- The union of all nonzero reducta of the polynomials in `A`. -/
noncomputable def reductaSet (A : Finset (MvPolynomial (Fin (r + 1)) ℝ)) :
    Finset (Polynomial (MvPolynomial (Fin r) ℝ)) :=
  A.biUnion reducta

/-- Leading coefficients of a family of univariate polynomials. -/
noncomputable def projL (C : Finset (Polynomial (MvPolynomial (Fin r) ℝ))) :
    Finset (MvPolynomial (Fin r) ℝ) :=
  C.image Polynomial.leadingCoeff

/-- Principal subresultant coefficients of each polynomial with its derivative. -/
noncomputable def projS1 (C : Finset (Polynomial (MvPolynomial (Fin r) ℝ))) :
    Finset (MvPolynomial (Fin r) ℝ) :=
  C.biUnion fun B =>
    (Finset.range B.derivative.natDegree).image fun j => psc B B.derivative j

/-- Principal subresultant coefficients of pairs of polynomials. -/
noncomputable def projS2 (C : Finset (Polynomial (MvPolynomial (Fin r) ℝ))) :
    Finset (MvPolynomial (Fin r) ℝ) :=
  C.biUnion fun B₁ =>
    C.biUnion fun B₂ =>
      (Finset.range (min B₁.natDegree B₂.natDegree)).image fun j => psc B₁ B₂ j

/-- Collins' projection $\mathcal L\cup\mathcal S_1\cup\mathcal S_2$. -/
noncomputable def collinsProj (A : Finset (MvPolynomial (Fin (r + 1)) ℝ)) :
    Finset (MvPolynomial (Fin r) ℝ) :=
  projL (reductaSet A) ∪ projS1 (reductaSet A) ∪ projS2 (reductaSet A)

@[simp] theorem mem_reductaSet {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {B : Polynomial (MvPolynomial (Fin r) ℝ)} :
    B ∈ reductaSet A ↔ ∃ P ∈ A, ∃ k ≤ (finLastEquiv ℝ r P).support.card,
      reductum k (finLastEquiv ℝ r P) ≠ 0 ∧ B = reductum k (finLastEquiv ℝ r P) := by
  simp [reductaSet, reducta, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  aesop

@[simp] theorem mem_projL {C : Finset (Polynomial (MvPolynomial (Fin r) ℝ))}
    {Q : MvPolynomial (Fin r) ℝ} :
    Q ∈ projL C ↔ ∃ B ∈ C, B.leadingCoeff = Q := by
  simp [projL, Finset.mem_image]

@[simp] theorem mem_projS1 {C : Finset (Polynomial (MvPolynomial (Fin r) ℝ))}
    {Q : MvPolynomial (Fin r) ℝ} :
    Q ∈ projS1 C ↔ ∃ B ∈ C, ∃ j < B.derivative.natDegree,
      psc B B.derivative j = Q := by
  simp [projS1, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]

@[simp] theorem mem_projS2 {C : Finset (Polynomial (MvPolynomial (Fin r) ℝ))}
    {Q : MvPolynomial (Fin r) ℝ} :
    Q ∈ projS2 C ↔ ∃ B₁ ∈ C, ∃ B₂ ∈ C, ∃ j < min B₁.natDegree B₂.natDegree,
      psc B₁ B₂ j = Q := by
  simp [projS2, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]

@[simp] theorem mem_collinsProj {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {Q : MvPolynomial (Fin r) ℝ} :
    Q ∈ collinsProj A ↔
      Q ∈ projL (reductaSet A) ∨ Q ∈ projS1 (reductaSet A) ∨
        Q ∈ projS2 (reductaSet A) := by
  simp [collinsProj]

/-- Every nonzero reductum of a member belongs to the reducta set. -/
theorem reductum_mem_reductaSet {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {P : MvPolynomial (Fin (r + 1)) ℝ} (hP : P ∈ A) {k : ℕ}
    (hne : reductum k (finLastEquiv ℝ r P) ≠ 0) :
    reductum k (finLastEquiv ℝ r P) ∈ reductaSet A := by
  apply mem_reductaSet.mpr
  have hk : k ≤ (finLastEquiv ℝ r P).support.card := by
    by_contra h
    exact hne (reductum_eq_zero_of_support_card_le (finLastEquiv ℝ r P) (by omega))
  exact ⟨P, hP, k, hk, hne, rfl⟩

/-- Members of the reducta set are nonzero. -/
theorem ne_zero_of_mem_reductaSet {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {B : Polynomial (MvPolynomial (Fin r) ℝ)} (hB : B ∈ reductaSet A) : B ≠ 0 := by
  rcases mem_reductaSet.mp hB with ⟨_, _, _, _, hne, heq⟩
  simpa [heq] using hne

/-- The leading coefficient of a reductum belongs to `projL`. -/
theorem leadingCoeff_mem_projL {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {B : Polynomial (MvPolynomial (Fin r) ℝ)} (hB : B ∈ reductaSet A) :
    B.leadingCoeff ∈ projL (reductaSet A) :=
  mem_projL.mpr ⟨B, hB, rfl⟩

/-- The leading coefficient of a reductum belongs to the full projection. -/
theorem leadingCoeff_mem_collinsProj {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {B : Polynomial (MvPolynomial (Fin r) ℝ)} (hB : B ∈ reductaSet A) :
    B.leadingCoeff ∈ collinsProj A :=
  mem_collinsProj.mpr (Or.inl (leadingCoeff_mem_projL hB))

/-- A derivative PSC of a reductum belongs to the full projection. -/
theorem psc_self_derivative_mem_collinsProj
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {B : Polynomial (MvPolynomial (Fin r) ℝ)} (hB : B ∈ reductaSet A) {j : ℕ}
    (hj : j < B.derivative.natDegree) : psc B B.derivative j ∈ collinsProj A :=
  mem_collinsProj.mpr (Or.inr (Or.inl (mem_projS1.mpr ⟨B, hB, j, hj, rfl⟩)))

/-- A pairwise PSC of reducta belongs to the full projection. -/
theorem psc_mem_collinsProj {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {B₁ B₂ : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hB₁ : B₁ ∈ reductaSet A) (hB₂ : B₂ ∈ reductaSet A) {j : ℕ}
    (hj : j < min B₁.natDegree B₂.natDegree) : psc B₁ B₂ j ∈ collinsProj A :=
  mem_collinsProj.mpr (Or.inr (Or.inr
    (mem_projS2.mpr ⟨B₁, hB₁, B₂, hB₂, j, hj, rfl⟩)))

/-- The reducta set is monotone in the input polynomial set. -/
theorem reductaSet_mono {A B : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    (h : A ⊆ B) : reductaSet A ⊆ reductaSet B := by
  intro C hC
  rcases mem_reductaSet.mp hC with ⟨P, hP, k, hk, hne, heq⟩
  exact mem_reductaSet.mpr ⟨P, h hP, k, hk, hne, heq⟩

/-- Collins' projection is monotone in the input polynomial set. -/
theorem collinsProj_mono {A B : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    (h : A ⊆ B) : collinsProj A ⊆ collinsProj B := by
  intro Q hQ
  have hred := reductaSet_mono h
  rcases mem_collinsProj.mp hQ with hL | hS1 | hS2
  · rcases mem_projL.mp hL with ⟨B, hB, hQ⟩
    exact mem_collinsProj.mpr (Or.inl (mem_projL.mpr ⟨B, hred hB, hQ⟩))
  · rcases mem_projS1.mp hS1 with ⟨B, hB, j, hj, hQ⟩
    exact mem_collinsProj.mpr (Or.inr (Or.inl
      (mem_projS1.mpr ⟨B, hred hB, j, hj, hQ⟩)))
  · rcases mem_projS2.mp hS2 with ⟨B₁, hB₁, B₂, hB₂, j, hj, hQ⟩
    exact mem_collinsProj.mpr (Or.inr (Or.inr
      (mem_projS2.mpr ⟨B₁, hred hB₁, B₂, hred hB₂, j, hj, hQ⟩)))

end CollinsCAD
