import Logic.QuantifierStep
import CAD.AugmentedDecomp

namespace CollinsCAD

open FirstOrder FirstOrder.Language Polynomial MvPolynomial

/-- A quantifier prefix with fixed matrix arity. Constructors remove one
    bound variable from the output arity. -/
inductive Prefix (α : Type*) : ℕ → ℕ → Type where
  | nil {r : ℕ} : Prefix α r r
  | all {r o : ℕ} (p : Prefix α r (o + 1)) : Prefix α r o
  | ex {r o : ℕ} (p : Prefix α r (o + 1)) : Prefix α r o

/-- Apply a prefix to its quantifier-free matrix. -/
def Prefix.apply {α : Type*} {r o : ℕ} :
    Prefix α r o → orderedRing.BoundedFormula α r →
      orderedRing.BoundedFormula α o
  | .nil, χ => χ
  | .all p, χ => (p.apply χ).all
  | .ex p, χ => (p.apply χ).ex

/-- Descend through the CAD levels eliminated by a prefix. -/
def Prefix.dropCAD {α : Type*} {n r o : ℕ} :
    Prefix α r o → CAD (n + r) → CAD (n + o)
  | .nil, T => T
  | .all p, T => (p.dropCAD T).previous
  | .ex p, T => (p.dropCAD T).previous

/-- Project the augmented polynomial family through the same levels. -/
noncomputable def Prefix.projectFamily {α : Type*} {n r o : ℕ} :
    Prefix α r o → Finset (MvPolynomial (Fin (n + r)) ℝ) →
      Finset (MvPolynomial (Fin (n + o)) ℝ)
  | .nil, A => A
  | .all p, A => augProj (p.projectFamily A)
  | .ex p, A => augProj (p.projectFamily A)

/-- CAD validity is preserved by prefix descent. -/
theorem Prefix.dropCAD_valid {α : Type*} {n r o : ℕ}
    (pre : Prefix α r o) (T : CAD (n + r)) (hT : IsCAD T) :
    IsCAD (pre.dropCAD T) := by
  induction pre with
  | nil => exact hT
  | all p ih => exact IsCAD.previous ih
  | ex p ih => exact IsCAD.previous ih

/-- Augmented provenance is preserved by prefix descent. -/
theorem Prefix.dropCAD_provenance {α : Type*} {n r o : ℕ}
    (pre : Prefix α r o) (T : CAD (n + r))
    (A : Finset (MvPolynomial (Fin (n + r)) ℝ))
    (hprov : HasAugmentedProvenance T A) :
    HasAugmentedProvenance (pre.dropCAD T) (pre.projectFamily A) := by
  induction pre with
  | nil => exact hprov
  | all p ih => exact HasAugmentedProvenance.previous ih
  | ex p ih => exact HasAugmentedProvenance.previous ih

/-- Projected augmented families preserve integer coefficients. -/
theorem Prefix.projectFamily_isIntPolyFamily {α : Type*} {n r o : ℕ}
    (pre : Prefix α r o) (A : Finset (MvPolynomial (Fin (n + r)) ℝ))
    (hA : IsIntPolyFamily A) : IsIntPolyFamily (pre.projectFamily A) := by
  induction pre with
  | nil => exact hA
  | all p ih =>
    intro Q hQ
    exact isIntPoly_of_mem_augProj ih hQ
  | ex p ih =>
    intro Q hQ
    exact isIntPoly_of_mem_augProj ih hQ

/-- A syntactic view of a prenex formula as a prefix and QF matrix. -/
structure PrenexView (α : Type*) (m : ℕ)
    (φ : orderedRing.BoundedFormula α m) where
  matrixArity : ℕ
  prenex : Prefix α matrixArity m
  matrix : orderedRing.BoundedFormula α matrixArity
  matrix_qf : matrix.IsQF
  formula_eq : prenex.apply matrix = φ

/-- Every prenex formula has a prefix/matrix view. -/
theorem PrenexView.exists {α : Type*} {m : ℕ}
    {φ : orderedRing.BoundedFormula α m} (hφ : φ.IsPrenex) :
    Nonempty (PrenexView α m φ) := by
  induction hφ with
  | @of_isQF n φ h =>
    exact ⟨⟨n, .nil, φ, h, rfl⟩⟩
  | all h ih =>
    rcases ih with ⟨r, pre, χ, hχ, heq⟩
    exact ⟨⟨r, .all pre, χ, hχ, by simp [Prefix.apply, heq]⟩⟩
  | ex h ih =>
    rcases ih with ⟨r, pre, χ, hχ, heq⟩
    exact ⟨⟨r, .ex pre, χ, hχ, by simp [Prefix.apply, heq]⟩⟩

end CollinsCAD
