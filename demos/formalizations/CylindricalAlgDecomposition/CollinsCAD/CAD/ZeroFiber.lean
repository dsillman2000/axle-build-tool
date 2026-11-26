import Mathlib
import CAD.EffectiveReductum
import CAD.SignInvariant
import CAD.Lifting

namespace CollinsCAD

open Polynomial MvPolynomial

/-- Factors whose fibre at the base point is nonzero. On a projection-invariant
    connected set, these are exactly the factors with nowhere-zero fibres. -/
noncomputable def nonzeroFibers {r : ℕ}
    (A : Finset (MvPolynomial (Fin (r + 1)) ℝ)) (a₀ : Fin r → ℝ) :
    Finset (MvPolynomial (Fin (r + 1)) ℝ) := by
  classical
  exact A.filter (fun P => fiberPoly r P a₀ ≠ 0)

@[simp] theorem mem_nonzeroFibers {r : ℕ}
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} {a₀ : Fin r → ℝ}
    {P : MvPolynomial (Fin (r + 1)) ℝ} :
    P ∈ nonzeroFibers A a₀ ↔ P ∈ A ∧ fiberPoly r P a₀ ≠ 0 := by
  simp [nonzeroFibers]

/-- The nonzero-fibre filter is a subset of the original family. -/
theorem nonzeroFibers_subset {r : ℕ}
    (A : Finset (MvPolynomial (Fin (r + 1)) ℝ)) (a₀ : Fin r → ℝ) :
    nonzeroFibers A a₀ ⊆ A := by
  intro P hP
  exact (mem_nonzeroFibers.mp hP).1

/-- A specialization with nonzero leading coefficient is nonzero. -/
theorem map_eval_ne_zero_of_leadingCoeff_ne_zero {r : ℕ}
    (B : Polynomial (MvPolynomial (Fin r) ℝ)) (a : Fin r → ℝ)
    (h : MvPolynomial.eval a B.leadingCoeff ≠ 0) :
    B.map (MvPolynomial.eval a) ≠ 0 := by
  intro hz
  apply h
  have hc := congrArg (fun q : Polynomial ℝ => q.coeff B.natDegree) hz
  simpa [Polynomial.coeff_map, Polynomial.coeff_natDegree] using hc

/-- A factor retained by the base-point filter has nowhere-zero fibres on a
    projection-invariant base set. -/
theorem fiberPoly_ne_zero_of_mem_nonzeroFibers {r : ℕ}
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} {S : Set (Fin r → ℝ)}
    {a₀ : Fin r → ℝ} (ha₀ : a₀ ∈ S)
    (hproj : SignInvariant (collinsProj A) S)
    {P : MvPolynomial (Fin (r + 1)) ℝ} (hP : P ∈ nonzeroFibers A a₀) :
    ∀ a ∈ S, fiberPoly r P a ≠ 0 := by
  have hPA : P ∈ A := (mem_nonzeroFibers.mp hP).1
  have hbase : fiberPoly r P a₀ ≠ 0 := (mem_nonzeroFibers.mp hP).2
  have hL : SignInvariant (projL (reductaSet A)) S :=
    signInvariant_projL_of_collinsProj hproj
  rcases projection_effective_reductum A P hPA S hL with hzero | ⟨k, hB0, hbridge, hBlc⟩
  · exact (hbase (hzero a₀ ha₀)).elim
  · intro a ha hz
    have hmapne := map_eval_ne_zero_of_leadingCoeff_ne_zero
      (reductum k (finLastEquiv ℝ r P)) a (hBlc a ha)
    exact hmapne ((hbridge a ha).symm.trans hz)

/-- A factor excluded by the base-point filter vanishes identically on the
    base set. -/
theorem fiberPoly_eq_zero_of_not_mem_nonzeroFibers {r : ℕ}
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} {S : Set (Fin r → ℝ)}
    {a₀ : Fin r → ℝ} (ha₀ : a₀ ∈ S)
    (hproj : SignInvariant (collinsProj A) S)
    {P : MvPolynomial (Fin (r + 1)) ℝ} (hPA : P ∈ A)
    (hnot : P ∉ nonzeroFibers A a₀) :
    ∀ a ∈ S, fiberPoly r P a = 0 := by
  have hbase : fiberPoly r P a₀ = 0 := by
    by_contra hne
    exact hnot (mem_nonzeroFibers.mpr ⟨hPA, hne⟩)
  have hL : SignInvariant (projL (reductaSet A)) S :=
    signInvariant_projL_of_collinsProj hproj
  rcases projection_effective_reductum A P hPA S hL with hzero | ⟨k, hB0, hbridge, hBlc⟩
  · exact hzero
  · exfalso
    have hmapne := map_eval_ne_zero_of_leadingCoeff_ne_zero
      (reductum k (finLastEquiv ℝ r P)) a₀ (hBlc a₀ ha₀)
    exact hmapne ((hbridge a₀ ha₀).symm.trans hbase)

/-- Projection sign invariance restricts to the nonzero-fibre filter. -/
theorem signInvariant_collinsProj_nonzeroFibers {r : ℕ}
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} {S : Set (Fin r → ℝ)}
    (a₀ : Fin r → ℝ) (hproj : SignInvariant (collinsProj A) S) :
    SignInvariant (collinsProj (nonzeroFibers A a₀)) S :=
  SignInvariant.mono hproj (collinsProj_mono (nonzeroFibers_subset A a₀))

/-- The zero-fibre filtering wrapper: every input factor is either delineable
    or vanishes identically, while the retained-factor product is delineable. -/
theorem exists_product_delineability_nonzeroFibers {r : ℕ}
    (A : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (S : Set (Fin r → ℝ)) (hS : IsConnected S)
    (hproj : SignInvariant (collinsProj A) S)
    (a₀ : Fin r → ℝ) (ha₀ : a₀ ∈ S) :
    (∀ P ∈ A, IsRealDelineable P S ∨ ∀ a ∈ S, fiberPoly r P a = 0) ∧
      IsRealDelineable (∏ P ∈ nonzeroFibers A a₀, P) S := by
  have hfiber : ∀ P ∈ nonzeroFibers A a₀, ∀ a ∈ S, fiberPoly r P a ≠ 0 :=
    fun P hP => fiberPoly_ne_zero_of_mem_nonzeroFibers ha₀ hproj hP
  have hproj' : SignInvariant (collinsProj (nonzeroFibers A a₀)) S :=
    signInvariant_collinsProj_nonzeroFibers a₀ hproj
  rcases exists_product_delineability_of_nonzero_fibers
    (nonzeroFibers A a₀) S hS hproj' hfiber with ⟨hDgood, hDprod⟩
  refine ⟨?_, hDprod⟩
  intro P hP
  by_cases hgood : P ∈ nonzeroFibers A a₀
  · exact Or.inl (hDgood P hgood)
  · exact Or.inr (fiberPoly_eq_zero_of_not_mem_nonzeroFibers ha₀ hproj hP hgood)

end CollinsCAD
