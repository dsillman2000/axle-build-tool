import Mathlib
import CAD.CylinderPartition
import Analysis.Delineability

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- The semantic finite-partition invariants of a CAD level. -/
structure Decomposition (r : ℕ) where
  cells : List (Cell r)
  cells_nodup : cells.Nodup
  cover : ∀ x : Fin r → ℝ, ∃ c ∈ cells, x ∈ c.carrier
  pairwise_disjoint : ∀ c ∈ cells, ∀ d ∈ cells,
    c ≠ d → Disjoint c.carrier d.carrier

/-- Raw List-based cylinder history. Validity is recorded separately by
    `IsCAD`, keeping the inductive recursor simple. -/
inductive CAD : ℕ → Type where
  | zero (decomposition : Decomposition 0) : CAD 0
  | succ {r : ℕ}
      (previous : CAD r)
      (decomposition : Decomposition (r + 1))
      (parentChildren : List (Cylinder r)) : CAD (r + 1)

/-- The semantic decomposition at a CAD level. -/
def CAD.decomposition : CAD r → Decomposition r
  | .zero d => d
  | .succ _ d _ => d

/-- The ordered list of cells at a CAD level. -/
def CAD.cells (T : CAD r) : List (Cell r) := T.decomposition.cells

/-- The preceding CAD level. -/
def CAD.previous : CAD (r + 1) → CAD r
  | .succ previous _ _ => previous

/-- The explicit parent-to-child cylinder map. -/
def CAD.parentChildren (T : CAD (r + 1)) : List (Cylinder r) :=
  match T with
  | .succ _ _ edges => edges

/-- A list of cylinders is a complete, unique parent-to-child map between
    two consecutive semantic decompositions. -/
def IsParentChildMap {r : ℕ}
    (D : Decomposition r) (E : Decomposition (r + 1))
    (edges : List (Cylinder r)) : Prop :=
  edges.Nodup ∧
    (∀ L ∈ edges, L.parent ∈ D.cells) ∧
    (∀ c ∈ D.cells, ∃ L ∈ edges, L.parent = c) ∧
    (∀ L ∈ edges, ∀ M ∈ edges, L.parent = M.parent → L = M) ∧
    E.cells = edges.flatMap (fun L => L.children) ∧
    (∀ L ∈ edges, IsCylinderPartition L)

/-- Recursive validity of a raw cylinder tree. -/
def IsCAD : {r : ℕ} → CAD r → Prop
  | 0, .zero _ => True
  | _ + 1, .succ previous next edges =>
      IsCAD previous ∧ IsParentChildMap previous.decomposition next edges

/-- The parent-to-child map component of a valid successor CAD. -/
theorem IsCAD.parentChildMap {T : CAD (r + 1)} (hT : IsCAD T) :
    IsParentChildMap T.previous.decomposition T.decomposition T.parentChildren := by
  cases T with
  | succ previous next edges => exact hT.2

/-- A polynomial family is invariant on every cell of a list. -/
def CADInvariant (A : Finset (MvPolynomial (Fin r) ℝ))
    (cells : List (Cell r)) : Prop :=
  ∀ c ∈ cells, SignInvariant A c.carrier

/-- Direct child lookup for later EVAL. Under `IsCAD`, exactly one cylinder
    has the requested parent. -/
noncomputable def CAD.childrenOf (T : CAD (r + 1)) (c : Cell r) :
    List (Cell (r + 1)) := by
  classical
  exact (T.parentChildren.filter (fun L => L.parent = c)).flatMap
    (fun L => L.children)

/-- Membership in the direct child list is exactly membership in the unique
    cylinder with the requested parent. -/
theorem IsCAD.mem_childrenOf {T : CAD (r + 1)} (_hT : IsCAD T)
    {c : Cell r} {d : Cell (r + 1)} :
    d ∈ T.childrenOf c ↔
      ∃ L ∈ T.parentChildren, L.parent = c ∧ d ∈ L.children := by
  classical
  simp [CAD.childrenOf, List.mem_flatMap, List.mem_filter, and_assoc]

/-- Direct children are cells of the next CAD level. -/
theorem IsCAD.childrenOf_subset_cells {T : CAD (r + 1)} (hT : IsCAD T)
    {c : Cell r} {d : Cell (r + 1)} (hd : d ∈ T.childrenOf c) : d ∈ T.cells := by
  have hmap := IsCAD.parentChildMap hT
  rcases (IsCAD.mem_childrenOf hT).mp hd with ⟨L, hL, _, hdL⟩
  have hmem : d ∈ T.parentChildren.flatMap (fun M => M.children) :=
    List.mem_flatMap.mpr ⟨L, hL, hdL⟩
  rw [← hmap.2.2.2.2.1] at hmem
  exact hmem

/-- Direct children cover every fibre over their parent cell. -/
theorem IsCAD.childrenOf_cover {T : CAD (r + 1)} (hT : IsCAD T)
    {c : Cell r} (hc : c ∈ T.previous.cells) {a : Fin r → ℝ}
    (ha : a ∈ c.carrier) (x : ℝ) :
    ∃ d ∈ T.childrenOf c, Fin.snoc a x ∈ d.carrier := by
  have hmap := IsCAD.parentChildMap hT
  rcases hmap.2.2.1 c hc with ⟨L, hL, rfl⟩
  rcases (hmap.2.2.2.2.2 L hL).1 a ha x with ⟨d, hd, hxd⟩
  exact ⟨d, (IsCAD.mem_childrenOf hT).mpr ⟨L, hL, rfl, hd⟩, hxd⟩

/-- Every direct child meets every fibre over its parent cell. -/
theorem IsCAD.childrenOf_fiber_nonempty {T : CAD (r + 1)} (hT : IsCAD T)
    {c : Cell r} {a : Fin r → ℝ} (ha : a ∈ c.carrier)
    {d : Cell (r + 1)} (hd : d ∈ T.childrenOf c) :
    ∃ x : ℝ, Fin.snoc a x ∈ d.carrier := by
  have hmap := IsCAD.parentChildMap hT
  rcases (IsCAD.mem_childrenOf hT).mp hd with ⟨L, hL, hparent, hdL⟩
  have ha' : a ∈ L.parent.carrier := by simpa [hparent] using ha
  exact (hmap.2.2.2.2.2 L hL).2.1 a ha' d hdL

/-- A direct child is nonempty whenever its parent occurs in the previous CAD. -/
theorem IsCAD.childrenOf_nonempty {T : CAD (r + 1)} (hT : IsCAD T)
    {c : Cell r} (hc : c ∈ T.previous.cells) : (T.childrenOf c) ≠ [] := by
  rcases IsCAD.childrenOf_cover hT hc c.sample_mem 0 with ⟨d, hd, _⟩
  exact List.ne_nil_of_mem hd

/-- Points in a direct child project into its parent cell. -/
theorem IsCAD.childrenOf_init_mem {T : CAD (r + 1)} (hT : IsCAD T)
    {c : Cell r} {d : Cell (r + 1)} (hd : d ∈ T.childrenOf c)
    {z : Fin (r + 1) → ℝ} (hz : z ∈ d.carrier) : Fin.init z ∈ c.carrier := by
  rcases (IsCAD.mem_childrenOf hT).mp hd with ⟨L, hL, hparent, hdL⟩
  have hzparent := LiftShape.init_mem (L.children_shape d hdL) hz
  simpa [hparent] using hzparent

/-- Validity descends to the preceding CAD level. -/
theorem IsCAD.previous {T : CAD (r + 1)} (hT : IsCAD T) : IsCAD T.previous := by
  cases T with
  | succ previous next edges => exact hT.1

/-- The unique zero-dimensional cell. -/
def baseCell0 : Cell 0 where
  carrier := Set.univ
  sample := Fin.elim0
  sample_mem := Set.mem_univ _
  connected := isConnected_univ

/-- The unique zero-dimensional decomposition. -/
def baseDecomposition0 : Decomposition 0 where
  cells := [baseCell0]
  cells_nodup := by simp
  cover := by
    intro x
    exact ⟨baseCell0, by simp, Set.mem_univ x⟩
  pairwise_disjoint := by simp

/-- The uniform base case for DECOMP. -/
def baseCAD : CAD 0 := .zero baseDecomposition0

/-- Every polynomial family is invariant on the zero-dimensional base cell. -/
theorem baseCAD_invariant (A : Finset (MvPolynomial (Fin 0) ℝ)) :
    CADInvariant A baseCAD.cells := by
  intro c hc
  have hc' : c ∈ [baseCell0] := by
    change c ∈ (CAD.zero baseDecomposition0).decomposition.cells at hc
    exact hc
  have hceq : c = baseCell0 := List.mem_singleton.mp hc'
  subst c
  intro P hP
  refine ⟨SignType.sign (MvPolynomial.eval baseCell0.sample P), ?_⟩
  intro a ha
  have haeq : a = baseCell0.sample := Subsingleton.elim _ _
  subst a
  rfl

end CollinsCAD
