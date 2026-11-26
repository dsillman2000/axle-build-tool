import Mathlib
import CAD.Cell
import Analysis.Delineability

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- A finite strictly ordered family of continuous real root functions. -/
structure RootFamily (S : Set (Fin r → ℝ)) where
  k : ℕ
  f : Fin k → (Fin r → ℝ) → ℝ
  continuous : ∀ i, ContinuousOn (f i) S
  ordered : ∀ (i j : Fin k) (a : Fin r → ℝ),
    a ∈ S → i < j → f i a < f j a

/-- The four possible shapes of a child of a lifted cylinder, plus the
    no-root whole cylinder. -/
inductive LiftShape (S : Cell r) (R : RootFamily S.carrier) : Cell (r + 1) → Prop where
  | whole (hk : R.k = 0) : LiftShape S R (Cell.whole S)
  | lower (i : Fin R.k) (hi : i.val = 0) :
      LiftShape S R (Cell.lower S (R.f i) (R.continuous i))
  | graph (i : Fin R.k) :
      LiftShape S R (Cell.graph S (R.f i) (R.continuous i))
  | bounded (i j : Fin R.k) (hj : j.val = i.val + 1) :
      LiftShape S R (Cell.bounded S (R.f i) (R.f j)
        (R.continuous i) (R.continuous j)
        (fun a ha => R.ordered i j a ha (by change i.val < j.val; omega)))
  | upper (i : Fin R.k) (hi : i.val + 1 = R.k) :
      LiftShape S R (Cell.upper S (R.f i) (R.continuous i))

/-- Recursive construction of the alternating list of `2k+1` lifted cells. -/
noncomputable def liftCellsAux (S : Cell r) :
    (k : ℕ) → (f : Fin k → (Fin r → ℝ) → ℝ) →
    (∀ i, ContinuousOn (f i) S.carrier) →
    (∀ (i j : Fin k) (a : Fin r → ℝ), a ∈ S.carrier → i < j → f i a < f j a) →
    List (Cell (r + 1))
  | 0, _, _, _ => [Cell.whole S]
  | k + 1, f, hc, ho =>
    let f' : Fin k → (Fin r → ℝ) → ℝ := fun i => f i.succ
    have hc' : ∀ i, ContinuousOn (f' i) S.carrier := fun i => hc i.succ
    have ho' : ∀ (i j : Fin k) (a : Fin r → ℝ),
        a ∈ S.carrier → i < j → f' i a < f' j a := by
      intro i j a ha hij
      exact ho i.succ j.succ a ha (by change i.val + 1 < j.val + 1; omega)
    let left : (Fin r → ℝ) → ℝ := f 0
    let newCells : List (Cell (r + 1)) :=
      if hk : 0 < k then
        let right : (Fin r → ℝ) → ℝ := f ⟨1, by omega⟩
        [Cell.lower S left (hc 0),
          Cell.graph S left (hc 0),
          Cell.bounded S left right (hc 0) (hc ⟨1, by omega⟩)
            (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by change 0 < 1; omega))]
      else
        [Cell.lower S left (hc 0), Cell.graph S left (hc 0),
          Cell.upper S left (hc 0)]
    newCells ++ (liftCellsAux S k f' hc' ho').tail

/-- The canonical alternating child list of a root family. -/
noncomputable def liftCells (S : Cell r) (R : RootFamily S.carrier) :
    List (Cell (r + 1)) :=
  liftCellsAux S R.k R.f R.continuous R.ordered

/-- A parent cell, its ordered root family, and the resulting child cells. -/
structure Cylinder (r : ℕ) where
  parent : Cell r
  roots : RootFamily parent.carrier
  family : Finset (MvPolynomial (Fin (r + 1)) ℝ)
  children : List (Cell (r + 1))
  children_length : children.length = 2 * roots.k + 1
  children_shape : ∀ c ∈ children, LiftShape parent roots c
  invariant : ∀ c ∈ children, SignInvariant family c.carrier
  section_root : ∀ i a, a ∈ parent.carrier →
    ∃ P ∈ family, Polynomial.eval (roots.f i a) (fiberPoly r P a) = 0

/-- Semantic partition invariants for one lifted cylinder. -/
def IsCylinderPartition (L : Cylinder r) : Prop :=
  (∀ a ∈ L.parent.carrier, ∀ x : ℝ,
      ∃ c ∈ L.children, Fin.snoc a x ∈ c.carrier) ∧
  (∀ a ∈ L.parent.carrier, ∀ c ∈ L.children,
      ∃ x : ℝ, Fin.snoc a x ∈ c.carrier) ∧
  (∀ c ∈ L.children, ∀ d ∈ L.children,
      c ≠ d → Disjoint c.carrier d.carrier) ∧
  L.children.Nodup ∧
  (∀ c ∈ L.children, Fin.init c.sample = L.parent.sample)

end CollinsCAD
