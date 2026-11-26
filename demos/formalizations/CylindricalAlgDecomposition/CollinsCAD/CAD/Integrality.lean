import Mathlib
import CAD.AugmentedProjection

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- The canonical coefficient cast from integer to real multivariate
    polynomials. -/
noncomputable def intCastMv (r : ℕ) :
    MvPolynomial (Fin r) ℤ →+* MvPolynomial (Fin r) ℝ :=
  MvPolynomial.map (Int.castRingHom ℝ)

/-- The canonical coefficient cast for univariate polynomials with integer
    multivariate coefficients. -/
noncomputable def intCastUP (r : ℕ) :
    Polynomial (MvPolynomial (Fin r) ℤ) →+*
      Polynomial (MvPolynomial (Fin r) ℝ) :=
  Polynomial.mapRingHom (intCastMv r)

/-- A real multivariate polynomial has integer coefficients. -/
def IsIntPoly (P : MvPolynomial (Fin r) ℝ) : Prop :=
  ∃ P₀ : MvPolynomial (Fin r) ℤ, P = intCastMv r P₀

/-- A univariate polynomial all of whose multivariate coefficients have
    integer coefficients. -/
def IsIntUPoly (B : Polynomial (MvPolynomial (Fin r) ℝ)) : Prop :=
  ∃ B₀ : Polynomial (MvPolynomial (Fin r) ℤ), B = intCastUP r B₀

/-- The integer coefficient cast is injective. -/
theorem intCastMv_injective : Function.Injective (intCastMv r) :=
  MvPolynomial.map_injective (f := Int.castRingHom ℝ) Int.cast_injective

/-- Every integer polynomial is an integral real polynomial. -/
theorem isIntPoly_map (P : MvPolynomial (Fin r) ℤ) : IsIntPoly (intCastMv r P) :=
  ⟨P, rfl⟩

/-- The zero polynomial is integral. -/
theorem isIntPoly_zero : IsIntPoly (0 : MvPolynomial (Fin r) ℝ) :=
  ⟨0, by simp [intCastMv]⟩

/-- Integral polynomials are closed under addition. -/
theorem IsIntPoly.add {P Q : MvPolynomial (Fin r) ℝ}
    (hP : IsIntPoly P) (hQ : IsIntPoly Q) : IsIntPoly (P + Q) := by
  rcases hP with ⟨P₀, rfl⟩
  rcases hQ with ⟨Q₀, rfl⟩
  exact ⟨P₀ + Q₀, by simp [intCastMv]⟩

/-- Integral polynomials are closed under multiplication. -/
theorem IsIntPoly.mul {P Q : MvPolynomial (Fin r) ℝ}
    (hP : IsIntPoly P) (hQ : IsIntPoly Q) : IsIntPoly (P * Q) := by
  rcases hP with ⟨P₀, rfl⟩
  rcases hQ with ⟨Q₀, rfl⟩
  exact ⟨P₀ * Q₀, by simp [intCastMv]⟩

/-- Integral polynomials are closed under negation. -/
theorem IsIntPoly.neg {P : MvPolynomial (Fin r) ℝ}
    (hP : IsIntPoly P) : IsIntPoly (-P) := by
  rcases hP with ⟨P₀, rfl⟩
  exact ⟨-P₀, by simp [intCastMv]⟩

/-- Integral polynomials are closed under subtraction. -/
theorem IsIntPoly.sub {P Q : MvPolynomial (Fin r) ℝ}
    (hP : IsIntPoly P) (hQ : IsIntPoly Q) : IsIntPoly (P - Q) := by
  rcases hP with ⟨P₀, rfl⟩
  rcases hQ with ⟨Q₀, rfl⟩
  exact ⟨P₀ - Q₀, by simp [intCastMv, sub_eq_add_neg]⟩

/-- Every integral univariate coefficient polynomial is integral. -/
theorem isIntUPoly_map (B : Polynomial (MvPolynomial (Fin r) ℤ)) :
    IsIntUPoly (intCastUP r B) :=
  ⟨B, rfl⟩

/-- The zero univariate coefficient polynomial is integral. -/
theorem isIntUPoly_zero : IsIntUPoly (0 : Polynomial (MvPolynomial (Fin r) ℝ)) :=
  ⟨0, by simp [intCastUP]⟩

/-- Integral univariate coefficient polynomials are closed under addition. -/
theorem IsIntUPoly.add {B C : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hB : IsIntUPoly B) (hC : IsIntUPoly C) : IsIntUPoly (B + C) := by
  rcases hB with ⟨B₀, rfl⟩
  rcases hC with ⟨C₀, rfl⟩
  exact ⟨B₀ + C₀, by simp [intCastUP]⟩

/-- Integral univariate coefficient polynomials are closed under multiplication. -/
theorem IsIntUPoly.mul {B C : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hB : IsIntUPoly B) (hC : IsIntUPoly C) : IsIntUPoly (B * C) := by
  rcases hB with ⟨B₀, rfl⟩
  rcases hC with ⟨C₀, rfl⟩
  exact ⟨B₀ * C₀, by simp [intCastUP]⟩

/-- Integral univariate coefficient polynomials are closed under negation. -/
theorem IsIntUPoly.neg {B : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hB : IsIntUPoly B) : IsIntUPoly (-B) := by
  rcases hB with ⟨B₀, rfl⟩
  exact ⟨-B₀, by simp [intCastUP]⟩

/-- Integral univariate coefficient polynomials are closed under subtraction. -/
theorem IsIntUPoly.sub {B C : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hB : IsIntUPoly B) (hC : IsIntUPoly C) : IsIntUPoly (B - C) := by
  rcases hB with ⟨B₀, rfl⟩
  rcases hC with ⟨C₀, rfl⟩
  exact ⟨B₀ - C₀, by simp [intCastUP, sub_eq_add_neg]⟩

/-- Differentiation preserves integrality of univariate coefficient
    polynomials. -/
theorem IsIntUPoly.derivative {B : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hB : IsIntUPoly B) : IsIntUPoly B.derivative := by
  rcases hB with ⟨B₀, rfl⟩
  refine ⟨B₀.derivative, ?_⟩
  change (B₀.map (intCastMv r)).derivative = (B₀.derivative).map (intCastMv r)
  rw [Polynomial.derivative_map]

/-- Leading coefficients preserve integrality. -/
theorem IsIntUPoly.leadingCoeff {B : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hB : IsIntUPoly B) : IsIntPoly B.leadingCoeff := by
  rcases hB with ⟨B₀, rfl⟩
  refine ⟨B₀.leadingCoeff, ?_⟩
  change (B₀.map (intCastMv r)).leadingCoeff = intCastMv r B₀.leadingCoeff
  exact Polynomial.leadingCoeff_map_of_injective intCastMv_injective B₀

/-- Erasing the leading term commutes with the integer coefficient cast. -/
theorem eraseLead_map_int (B : Polynomial (MvPolynomial (Fin r) ℤ)) :
    (intCastUP r B).eraseLead = intCastUP r B.eraseLead := by
  have hdeg (D : Polynomial (MvPolynomial (Fin r) ℤ)) :
      (D.map (intCastMv r)).natDegree = D.natDegree :=
    Polynomial.natDegree_map_eq_of_injective intCastMv_injective D
  ext n
  simp only [intCastUP, Polynomial.coe_mapRingHom]
  rw [Polynomial.eraseLead_coeff, hdeg B]
  simp only [Polynomial.coeff_map, Polynomial.eraseLead_coeff]
  by_cases hn : n = B.natDegree <;> simp [hn, intCastMv]

/-- Reducta commute with the integer coefficient cast. -/
theorem reductum_map_int (k : ℕ) (B : Polynomial (MvPolynomial (Fin r) ℤ)) :
    reductum k (intCastUP r B) = intCastUP r (reductum k B) := by
  induction k with
  | zero =>
    change B.map (intCastMv r) = B.map (intCastMv r)
    rfl
  | succ k ih => simp [reductum_succ, ih, eraseLead_map_int]

/-- Iterated differentiation preserves integrality. -/
theorem IsIntUPoly.derivativeIter {B : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hB : IsIntUPoly B) (j : ℕ) : IsIntUPoly (derivativeIter j B) := by
  rcases hB with ⟨B₀, rfl⟩
  induction j with
  | zero => exact ⟨B₀, rfl⟩
  | succ j ih =>
    rw [derivativeIter_succ]
    exact ih.derivative

/-- Last-variable splitting preserves integrality. -/
theorem IsIntPoly.lastSplit {P : MvPolynomial (Fin (r + 1)) ℝ}
    (hP : IsIntPoly P) : IsIntUPoly (finLastEquiv ℝ r P) := by
  rcases hP with ⟨P₀, rfl⟩
  refine ⟨finLastEquiv ℤ r P₀, ?_⟩
  simpa [intCastUP, intCastMv] using
    finLastEquiv_map (Int.castRingHom ℝ) r P₀

/-- Inverse last-variable splitting preserves integrality. -/
theorem IsIntUPoly.lastUnsplit {B : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hB : IsIntUPoly B) : IsIntPoly ((finLastEquiv ℝ r).symm B) := by
  rcases hB with ⟨B₀, rfl⟩
  refine ⟨(finLastEquiv ℤ r).symm B₀, ?_⟩
  simpa [intCastUP, intCastMv] using
    finLastEquiv_symm_map (Int.castRingHom ℝ) r B₀

/-- Reducta of integral multivariate polynomials are integral. -/
theorem IsIntPoly.lastReductum {P : MvPolynomial (Fin (r + 1)) ℝ}
    (hP : IsIntPoly P) (k : ℕ) :
    IsIntUPoly (reductum k (finLastEquiv ℝ r P)) := by
  rcases IsIntPoly.lastSplit hP with ⟨B, hB⟩
  rw [hB]
  exact ⟨reductum k B, reductum_map_int k B⟩

/-- Principal subresultant coefficients preserve integrality when both
    coefficient polynomials are nonzero. -/
theorem IsIntUPoly.principalSubresultant {B C : Polynomial (MvPolynomial (Fin r) ℝ)}
    (hB : IsIntUPoly B) (hC : IsIntUPoly C) (hB₀ : B ≠ 0) (hC₀ : C ≠ 0)
    (j : ℕ) : IsIntPoly (psc B C j) := by
  rcases hB with ⟨B₀, rfl⟩
  rcases hC with ⟨C₀, rfl⟩
  have hB₀ne : B₀ ≠ 0 := by
    intro hz
    apply hB₀
    simp [hz, intCastUP]
  have hC₀ne : C₀ ≠ 0 := by
    intro hz
    apply hC₀
    simp [hz, intCastUP]
  have hlcB₀ : B₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hB₀ne
  have hlcC₀ : C₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hC₀ne
  have hlcB : (intCastMv r) B₀.leadingCoeff ≠ 0 := by
    intro hz
    exact hlcB₀ (intCastMv_injective (by simpa [intCastMv] using hz))
  have hlcC : (intCastMv r) C₀.leadingCoeff ≠ 0 := by
    intro hz
    exact hlcC₀ (intCastMv_injective (by simpa [intCastMv] using hz))
  refine ⟨psc B₀ C₀ j, ?_⟩
  simpa [intCastUP, intCastMv] using
    (psc_map (intCastMv r) B₀ C₀ j (Or.inl hlcB) (Or.inl hlcC)).symm

/-- Integrality of every member of a finite family. -/
def IsIntPolyFamily (A : Finset (MvPolynomial (Fin r) ℝ)) : Prop :=
  ∀ P ∈ A, IsIntPoly P

/-- Members of the reducta set of an integral family are integral. -/
theorem isIntUPoly_of_mem_reductaSet
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} (hA : IsIntPolyFamily A)
    {B : Polynomial (MvPolynomial (Fin r) ℝ)} (hB : B ∈ reductaSet A) :
    IsIntUPoly B := by
  rcases mem_reductaSet.mp hB with ⟨P, hP, k, hk, hne, rfl⟩
  exact IsIntPoly.lastReductum (hA P hP) k

/-- Leading-coefficient projection preserves integrality. -/
theorem isIntPoly_of_mem_projL
    {C : Finset (Polynomial (MvPolynomial (Fin r) ℝ))}
    (hC : ∀ B ∈ C, IsIntUPoly B) {Q : MvPolynomial (Fin r) ℝ}
    (hQ : Q ∈ projL C) : IsIntPoly Q := by
  rcases mem_projL.mp hQ with ⟨B, hB, rfl⟩
  exact IsIntUPoly.leadingCoeff (hC B hB)

/-- Self-derivative PSC projection preserves integrality. -/
theorem isIntPoly_of_mem_projS1
    {C : Finset (Polynomial (MvPolynomial (Fin r) ℝ))}
    (hC : ∀ B ∈ C, IsIntUPoly B) (hCne : ∀ B ∈ C, B ≠ 0)
    {Q : MvPolynomial (Fin r) ℝ} (hQ : Q ∈ projS1 C) : IsIntPoly Q := by
  rcases mem_projS1.mp hQ with ⟨B, hB, j, hj, rfl⟩
  have hder : B.derivative ≠ 0 := by
    intro hz
    simp [hz] at hj
  exact IsIntUPoly.principalSubresultant (hC B hB)
    (IsIntUPoly.derivative (hC B hB)) (hCne B hB) hder j

/-- Pairwise PSC projection preserves integrality. -/
theorem isIntPoly_of_mem_projS2
    {C : Finset (Polynomial (MvPolynomial (Fin r) ℝ))}
    (hC : ∀ B ∈ C, IsIntUPoly B) (hCne : ∀ B ∈ C, B ≠ 0)
    {Q : MvPolynomial (Fin r) ℝ} (hQ : Q ∈ projS2 C) : IsIntPoly Q := by
  rcases mem_projS2.mp hQ with ⟨B₁, hB₁, B₂, hB₂, j, hj, rfl⟩
  exact IsIntUPoly.principalSubresultant (hC B₁ hB₁) (hC B₂ hB₂)
    (hCne B₁ hB₁) (hCne B₂ hB₂) j

/-- Collins projection preserves integrality. -/
theorem isIntPoly_of_mem_collinsProj
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} (hA : IsIntPolyFamily A)
    {Q : MvPolynomial (Fin r) ℝ} (hQ : Q ∈ collinsProj A) : IsIntPoly Q := by
  have hred : ∀ B ∈ reductaSet A, IsIntUPoly B :=
    fun B hB => isIntUPoly_of_mem_reductaSet hA hB
  have hredne : ∀ B ∈ reductaSet A, B ≠ 0 :=
    fun B hB => ne_zero_of_mem_reductaSet hB
  rcases mem_collinsProj.mp hQ with hL | hS1 | hS2
  · exact isIntPoly_of_mem_projL hred hL
  · exact isIntPoly_of_mem_projS1 hred hredne hS1
  · exact isIntPoly_of_mem_projS2 hred hredne hS2

/-- Members of the augmented polynomial envelope are integral. -/
theorem isIntPoly_of_mem_augPolySet
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} (hA : IsIntPolyFamily A)
    {Q : MvPolynomial (Fin (r + 1)) ℝ} (hQ : Q ∈ augPolySet A) : IsIntPoly Q := by
  rcases mem_augPolySet.mp hQ with hQA | ⟨B, hB, j, hj, hne, rfl⟩
  · exact hA Q hQA
  · exact IsIntUPoly.lastUnsplit
      (IsIntUPoly.derivativeIter (isIntUPoly_of_mem_reductaSet hA hB) j)

/-- Augmented projection preserves integrality. -/
theorem isIntPoly_of_mem_augProj
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} (hA : IsIntPolyFamily A)
    {Q : MvPolynomial (Fin r) ℝ} (hQ : Q ∈ augProj A) : IsIntPoly Q := by
  exact isIntPoly_of_mem_collinsProj
    (fun P hP => isIntPoly_of_mem_augPolySet hA hP) hQ

end CollinsCAD
