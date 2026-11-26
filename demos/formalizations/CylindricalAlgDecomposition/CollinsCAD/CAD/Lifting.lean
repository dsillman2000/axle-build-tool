import Mathlib
import CAD.LiftingCore

namespace CollinsCAD

open Polynomial

/-- Collins' Theorem 5: on a connected projection-invariant base set with
    nonzero fibres, all factor roots are exhausted by one finite strictly
    ordered family of continuous real functions. -/
theorem projection_fundamental_lifting
    {r : ℕ} (A : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (S : Set (Fin r → ℝ)) (hS : IsConnected S)
    (hproj : SignInvariant (collinsProj A) S)
    (hfiber : ∀ P ∈ A, ∀ a ∈ S, fiberPoly r P a ≠ 0) :
    (∀ P ∈ A, IsRealDelineable P S) ∧
      ∃ (k : ℕ) (f : Fin k → (Fin r → ℝ) → ℝ) (e : Fin k → ℕ),
        (∀ i, ContinuousOn (f i) S) ∧
        (∀ i a, a ∈ S → 0 < e i ∧
          Polynomial.eval (f i a) (fiberPoly r (∏ P ∈ A, P) a) = 0 ∧
          Polynomial.rootMultiplicity (f i a)
            (fiberPoly r (∏ P ∈ A, P) a) = e i) ∧
        (∀ a ∈ S, ∀ x : ℝ,
          Polynomial.eval x (fiberPoly r (∏ P ∈ A, P) a) = 0 → ∃ i, f i a = x) ∧
        (∀ (i j : Fin k) (a : Fin r → ℝ), a ∈ S → i < j → f i a < f j a) ∧
        (∀ a ∈ S, Set.range (fun i => f i a) =
          ⋃ P ∈ A, {x : ℝ | Polynomial.eval x (fiberPoly r P a) = 0}) := by
  classical
  rcases exists_product_delineability_of_nonzero_fibers A S hS hproj hfiber with
    ⟨hDall, hDprod⟩
  rcases hDprod with ⟨k, f, e, hcont, hroot, hexhaust, hmono⟩
  refine ⟨hDall, k, f, e, hcont, hroot, hexhaust, hmono, ?_⟩
  intro a ha
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    have hxprod := (hroot i a ha).2.1
    rcases (fiberPoly_eval_prod_eq_zero_iff A a (f i a)).mp hxprod with ⟨P, hP, hxP⟩
    exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP, hxP⟩⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨P, hxP⟩
    rcases Set.mem_iUnion.mp hxP with ⟨hP, hxP⟩
    have hxprod := (fiberPoly_eval_prod_eq_zero_iff A a x).mpr ⟨P, hP, hxP⟩
    rcases hexhaust a ha x hxprod with ⟨i, hi⟩
    exact ⟨i, hi⟩

/-- The product formulation of Collins' Theorem 5. -/
theorem projection_fundamental_lifting_product
    {r : ℕ} (A : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (S : Set (Fin r → ℝ)) (hS : IsConnected S)
    (hproj : SignInvariant (collinsProj A) S)
    (hfiber : ∀ P ∈ A, ∀ a ∈ S, fiberPoly r P a ≠ 0) :
    (∀ P ∈ A, IsRealDelineable P S) ∧
      IsRealDelineable (∏ P ∈ A, P) S :=
  exists_product_delineability_of_nonzero_fibers A S hS hproj hfiber

end CollinsCAD
