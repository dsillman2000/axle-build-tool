import Mathlib
import CAD.ProjectionDef
import CAD.ZeroFiber

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- Iterated formal derivative, with the iteration count first. -/
noncomputable def derivativeIter (j : ℕ) (B : Polynomial (MvPolynomial (Fin r) ℝ)) :
    Polynomial (MvPolynomial (Fin r) ℝ) :=
  Polynomial.derivative^[j] B

@[simp] theorem derivativeIter_zero (B : Polynomial (MvPolynomial (Fin r) ℝ)) :
    derivativeIter 0 B = B := by
  simp [derivativeIter]

@[simp] theorem derivativeIter_succ (j : ℕ) (B : Polynomial (MvPolynomial (Fin r) ℝ)) :
    derivativeIter (j + 1) B = (derivativeIter j B).derivative := by
  simp [derivativeIter, Function.iterate_succ_apply']

@[simp] theorem derivativeIter_add (j l : ℕ) (B : Polynomial (MvPolynomial (Fin r) ℝ)) :
    derivativeIter (j + l) B = derivativeIter l (derivativeIter j B) := by
  rw [Nat.add_comm j l]
  simp [derivativeIter, Function.iterate_add_apply]

/-- All nonzero iterated last-variable derivatives of `B`, including `B`
    itself and the final constant derivative. -/
noncomputable def derivativeTower (B : Polynomial (MvPolynomial (Fin r) ℝ)) :
    Finset (Polynomial (MvPolynomial (Fin r) ℝ)) := by
  classical
  exact ((Finset.range (B.natDegree + 1)).image
    (fun j => derivativeIter j B)).filter (· ≠ 0)

@[simp] theorem mem_derivativeTower {B D : Polynomial (MvPolynomial (Fin r) ℝ)} :
    D ∈ derivativeTower B ↔
      ∃ j ≤ B.natDegree, derivativeIter j B = D ∧ D ≠ 0 := by
  simp [derivativeTower, derivativeIter, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range]
  aesop

/-- A global finite envelope containing the original family and every
    effective-reductum derivative tower. -/
noncomputable def augPolySet (A : Finset (MvPolynomial (Fin (r + 1)) ℝ)) :
    Finset (MvPolynomial (Fin (r + 1)) ℝ) := by
  classical
  exact A ∪ (reductaSet A).biUnion fun B =>
    (derivativeTower B).image fun D => (finLastEquiv ℝ r).symm D

/-- The augmented projection. -/
noncomputable def augProj (A : Finset (MvPolynomial (Fin (r + 1)) ℝ)) :
    Finset (MvPolynomial (Fin r) ℝ) :=
  collinsProj (augPolySet A)

@[simp] theorem mem_augPolySet {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {Q : MvPolynomial (Fin (r + 1)) ℝ} :
    Q ∈ augPolySet A ↔ Q ∈ A ∨
      ∃ B ∈ reductaSet A, ∃ j ≤ B.natDegree,
        derivativeIter j B ≠ 0 ∧
        Q = (finLastEquiv ℝ r).symm (derivativeIter j B) := by
  constructor
  · intro hQ
    rcases Finset.mem_union.mp hQ with hQA | hQ
    · exact Or.inl hQA
    · rcases Finset.mem_biUnion.mp hQ with ⟨B, hB, hD⟩
      rcases Finset.mem_image.mp hD with ⟨D, hD, hEq⟩
      rcases mem_derivativeTower.mp hD with ⟨j, hj, hjD, hne⟩
      subst Q
      exact Or.inr ⟨B, hB, j, hj, by simpa [hjD] using hne, by rw [hjD]⟩
  · rintro (hQA | ⟨B, hB, j, hj, hne, rfl⟩)
    · exact Finset.mem_union_left _ hQA
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨B, hB, ?_⟩
      exact Finset.mem_image.mpr
        ⟨derivativeIter j B, mem_derivativeTower.mpr ⟨j, hj, rfl, hne⟩, rfl⟩

/-- The original family is contained in its augmented envelope. -/
theorem subset_augPolySet (A : Finset (MvPolynomial (Fin (r + 1)) ℝ)) :
    A ⊆ augPolySet A := by
  intro P hP
  exact mem_augPolySet.mpr (Or.inl hP)

/-- The augmented envelope is monotone. -/
theorem augPolySet_mono {A B : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    (h : A ⊆ B) : augPolySet A ⊆ augPolySet B := by
  intro Q hQ
  rcases mem_augPolySet.mp hQ with hQA | ⟨C, hC, j, hj, hne, rfl⟩
  · exact subset_augPolySet B (h hQA)
  · exact mem_augPolySet.mpr (Or.inr ⟨C, reductaSet_mono h hC, j, hj, hne, rfl⟩)

/-- The augmented projection is monotone. -/
theorem augProj_mono {A B : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    (h : A ⊆ B) : augProj A ⊆ augProj B :=
  collinsProj_mono (augPolySet_mono h)

/-- Ordinary projection is contained in augmented projection. -/
theorem collinsProj_subset_augProj (A : Finset (MvPolynomial (Fin (r + 1)) ℝ)) :
    collinsProj A ⊆ augProj A :=
  collinsProj_mono (subset_augPolySet A)

/-- Iterating a derivative of a tower element stays in the same tower. -/
theorem derivative_iterate_mem_tower
    (B : Polynomial (MvPolynomial (Fin r) ℝ)) (j l : ℕ)
    (hj : j ≤ B.natDegree) (hl : l ≤ (derivativeIter j B).natDegree)
    (hne : derivativeIter l
      (derivativeIter j B) ≠ 0) :
    derivativeIter l
      (derivativeIter j B) ∈ derivativeTower B := by
  have hdeg : (derivativeIter j B).natDegree ≤ B.natDegree - j := by
    simpa [derivativeIter] using Polynomial.natDegree_iterate_derivative B j
  have htotal : j + l ≤ B.natDegree := by omega
  apply mem_derivativeTower.mpr
  refine ⟨j + l, htotal, ?_, hne⟩
  exact derivativeIter_add j l B

/-- The augmented envelope contains every derivative of every member. -/
theorem symm_derivative_mem_augPolySet
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {Q : MvPolynomial (Fin (r + 1)) ℝ} (hQ : Q ∈ augPolySet A)
    {D : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hD : D ∈ derivativeTower (finLastEquiv ℝ r Q)) :
    (finLastEquiv ℝ r).symm D ∈ augPolySet A := by
  rcases mem_augPolySet.mp hQ with hQA | ⟨B, hB, j, hj, hjne, rfl⟩
  · by_cases hQ0 : Q = 0
    · subst Q
      rcases hD with ⟨hD0, hDne⟩
    · have hB0 : reductum 0 (finLastEquiv ℝ r Q) ≠ 0 := by
        simpa [reductum] using hQ0
      have hBmem : reductum 0 (finLastEquiv ℝ r Q) ∈ reductaSet A :=
        reductum_mem_reductaSet hQA hB0
      have hfin : finLastEquiv ℝ r Q = reductum 0 (finLastEquiv ℝ r Q) := by
        simp [reductum]
      rw [hfin] at hD
      rcases mem_derivativeTower.mp hD with ⟨l, hl, hDl, hDne⟩
      apply mem_augPolySet.mpr
      refine Or.inr ⟨reductum 0 (finLastEquiv ℝ r Q), hBmem, l, ?_, ?_, ?_⟩
      · simpa [reductum] using hl
      · simpa only [hDl] using hDne
      · rw [hDl]
  · have hfin : finLastEquiv ℝ r ((finLastEquiv ℝ r).symm
        (derivativeIter j B)) =
        derivativeIter j B := by simp
    rw [hfin] at hD
    rcases mem_derivativeTower.mp hD with ⟨l, hl, hDl, hDne⟩
    have hDmem : derivativeIter l (derivativeIter j B) ∈ derivativeTower B :=
      derivative_iterate_mem_tower B j l hj hl (by simpa only [hDl] using hDne)
    rcases mem_derivativeTower.mp hDmem with ⟨t, ht, hDt, hDtne⟩
    have hDtne' : derivativeIter t B ≠ 0 := by
      rw [hDt]
      exact hDtne
    apply mem_augPolySet.mpr
    refine Or.inr ⟨B, hB, t, ht, hDtne', ?_⟩
    rw [hDt, hDl]

/-- The cell-local augmented family. -/
noncomputable def localAugPolySet (A : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (a₀ : Fin r → ℝ) : Finset (MvPolynomial (Fin (r + 1)) ℝ) :=
  nonzeroFibers (augPolySet A) a₀

/-- Every local augmented polynomial has nowhere-zero fibres. -/
theorem fiberPoly_ne_zero_of_mem_localAugPolySet
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} {S : Set (Fin r → ℝ)}
    {a₀ : Fin r → ℝ} (ha₀ : a₀ ∈ S)
    (hproj : SignInvariant (augProj A) S)
    {Q : MvPolynomial (Fin (r + 1)) ℝ} (hQ : Q ∈ localAugPolySet A a₀) :
    ∀ a ∈ S, fiberPoly r Q a ≠ 0 := by
  exact fiberPoly_ne_zero_of_mem_nonzeroFibers ha₀ hproj hQ

/-- Projection invariance restricts to the local augmented family. -/
theorem signInvariant_collinsProj_localAugPolySet
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} {S : Set (Fin r → ℝ)}
    (a₀ : Fin r → ℝ) (hproj : SignInvariant (augProj A) S) :
    SignInvariant (collinsProj (localAugPolySet A a₀)) S := by
  exact SignInvariant.mono hproj
    (collinsProj_mono (nonzeroFibers_subset (augPolySet A) a₀))

/-- Derivatives of local augmented polynomials are either retained or vanish
    identically on the base cell. -/
theorem localAugPolySet_derivative_dichotomy
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} {S : Set (Fin r → ℝ)}
    {a₀ : Fin r → ℝ} (ha₀ : a₀ ∈ S)
    (hproj : SignInvariant (augProj A) S)
    {Q : MvPolynomial (Fin (r + 1)) ℝ} (hQ : Q ∈ localAugPolySet A a₀)
    {D : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hD : D ∈ derivativeTower (finLastEquiv ℝ r Q)) :
    (finLastEquiv ℝ r).symm D ∈ localAugPolySet A a₀ ∨
      (∀ a ∈ S, fiberPoly r ((finLastEquiv ℝ r).symm D) a = 0) := by
  have hQA : Q ∈ augPolySet A := (mem_nonzeroFibers.mp hQ).1
  have hDA : (finLastEquiv ℝ r).symm D ∈ augPolySet A :=
    symm_derivative_mem_augPolySet hQA hD
  by_cases hret : (finLastEquiv ℝ r).symm D ∈ localAugPolySet A a₀
  · exact Or.inl hret
  · exact Or.inr (fiberPoly_eq_zero_of_not_mem_nonzeroFibers ha₀ hproj hDA hret)

/-- Derivatives commute with fibre specialization. -/
theorem fiberPoly_derivative_iterate
    (Q : MvPolynomial (Fin (r + 1)) ℝ) (a : Fin r → ℝ) (j : ℕ) :
    fiberPoly r ((finLastEquiv ℝ r).symm
      (derivativeIter j (finLastEquiv ℝ r Q))) a =
      Polynomial.derivative^[j] (fiberPoly r Q a) := by
  induction j with
  | zero =>
    rw [derivativeIter_zero, fiberPoly_finLastEquiv_symm, Function.iterate_zero_apply]
    rfl
  | succ j ih =>
    rw [derivativeIter_succ, fiberPoly_finLastEquiv_symm,
      ← Polynomial.derivative_map, Function.iterate_succ_apply', ← ih,
      fiberPoly_finLastEquiv_symm]

end CollinsCAD
