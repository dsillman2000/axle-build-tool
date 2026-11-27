import Logic.Evaluation

namespace CollinsCAD

open FirstOrder FirstOrder.Language Polynomial MvPolynomial

/-- Appending a coordinate preserves the free part. -/
@[simp] theorem freePart_snoc {n m : ℕ} (z : Fin (n + m) → ℝ) (x : ℝ) :
    freePart (n := n) (m := m + 1) (Fin.snoc z x) =
      freePart (n := n) (m := m) z := by
  funext i
  simp [freePart]

/-- Appending a coordinate appends to the bound part. -/
@[simp] theorem boundPart_snoc {n m : ℕ} (z : Fin (n + m) → ℝ) (x : ℝ) :
    boundPart (n := n) (m := m + 1) (Fin.snoc z x) =
      Fin.snoc (boundPart (n := n) (m := m) z) x := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [boundPart]
  · change @Fin.snoc (n + m) (fun _ => ℝ) z x (Fin.natAdd n i).castSucc =
      @Fin.snoc m (fun _ => ℝ) (boundPart (n := n) (m := m) z) x i.castSucc
    rw [@Fin.snoc_castSucc (n + m) (fun _ => ℝ) x z (Fin.natAdd n i),
      @Fin.snoc_castSucc m (fun _ => ℝ) x (boundPart (n := n) (m := m) z) i]
    rfl

/-- Quantifier realization on a snoc tuple is bounded realization on the
    concatenated CAD coordinates. -/
theorem boundedRealize_snoc {n m : ℕ}
    (φ : orderedRing.BoundedFormula (Fin n) (m + 1))
    (z : Fin (n + m) → ℝ) (x : ℝ) :
    φ.Realize (freePart z) (Fin.snoc (boundPart z) x) ↔
      boundedRealize φ (Fin.snoc z x) := by
  rw [boundedRealize, freePart_snoc, boundPart_snoc]

/-- The two quantifier choices. -/
inductive Quantifier
  | all
  | ex

/-- Apply one quantifier to the last in-scope variable. -/
def Quantifier.apply {α : Type*} {m : ℕ} (q : Quantifier)
    (φ : orderedRing.BoundedFormula α (m + 1)) :
    orderedRing.BoundedFormula α m :=
  match q with
  | .all => φ.all
  | .ex => φ.ex

/-- Finite conjunction or disjunction over a child list. -/
def Quantifier.fold {β : Type*} (q : Quantifier) (P : β → Prop)
    (cs : List β) : Prop :=
  match q, cs with
  | Quantifier.all, cs => ∀ c ∈ cs, P c
  | Quantifier.ex, cs => ∃ c ∈ cs, P c

/-- One quantifier is the corresponding finite operation on bounded truths
    along the last-coordinate fibre. -/
theorem realize_quantifier_iff_boundedRealize {n m : ℕ} (q : Quantifier)
    (φ : orderedRing.BoundedFormula (Fin n) (m + 1))
    (z : Fin (n + m) → ℝ) :
    (q.apply φ).Realize (freePart z) (boundPart z) ↔
      match q with
      | .all => ∀ x : ℝ, boundedRealize φ (Fin.snoc z x)
      | .ex => ∃ x : ℝ, boundedRealize φ (Fin.snoc z x) := by
  cases q with
  | all =>
    simp only [Quantifier.apply, BoundedFormula.realize_all]
    apply forall_congr'
    intro x
    exact boundedRealize_snoc φ z x
  | ex =>
    simp only [Quantifier.apply, BoundedFormula.realize_ex]
    apply exists_congr
    intro x
    exact boundedRealize_snoc φ z x

/-- Collins' EVAL quantifier step: a quantified formula is evaluated by the
    finite conjunction/disjunction of child-sample truths. -/
theorem eval_quantifier_step {n m : ℕ} (q : Quantifier)
    (U : CAD (n + (m + 1))) (hU : IsCAD U)
    (φ : orderedRing.BoundedFormula (Fin n) (m + 1))
    (hconst : ∀ C ∈ U.cells, ConstantOnCell φ C)
    (S : Cell (n + m)) (hS : S ∈ U.previous.cells)
    (z : Fin (n + m) → ℝ) (hz : z ∈ S.carrier) :
    (q.apply φ).Realize (freePart z) (boundPart z) ↔
      q.fold (fun C => boundedRealize φ C.sample) (U.childrenOf S) := by
  rw [realize_quantifier_iff_boundedRealize]
  cases q with
  | all =>
    constructor
    · intro hall C hC
      rcases IsCAD.childrenOf_fiber_nonempty (c := S) (a := z) hU hz hC with ⟨x, hxC⟩
      exact (hconst C (IsCAD.childrenOf_subset_cells (c := S) hU hC) _ hxC).mp (hall x)
    · intro hchildren x
      rcases IsCAD.childrenOf_cover (c := S) (a := z) hU hS hz x with ⟨C, hC, hxC⟩
      exact (hconst C (IsCAD.childrenOf_subset_cells (c := S) hU hC) _ hxC).mpr
        (hchildren C hC)
  | ex =>
    constructor
    · rintro ⟨x, hx⟩
      rcases IsCAD.childrenOf_cover (c := S) (a := z) hU hS hz x with ⟨C, hC, hxC⟩
      exact ⟨C, hC, (hconst C (IsCAD.childrenOf_subset_cells (c := S) hU hC) _ hxC).mp hx⟩
    · rintro ⟨C, hC, hsample⟩
      rcases IsCAD.childrenOf_fiber_nonempty (c := S) (a := z) hU hz hC with ⟨x, hxC⟩
      exact ⟨x, (hconst C (IsCAD.childrenOf_subset_cells (c := S) hU hC) _ hxC).mpr hsample⟩

/-- Existential EVAL over one last variable. -/
theorem eval_exists_iff_children_of_constant {r : ℕ} {T : CAD (r + 1)}
    (hT : IsCAD T) {φ : orderedRing.BoundedFormula (Fin r) 1}
    (hconst : ∀ C ∈ T.cells, ConstantOnCell φ C)
    {c : Cell r} (hc : c ∈ T.previous.cells) {a : Fin r → ℝ}
    (ha : a ∈ c.carrier) :
    Formula.Realize (∃' φ) a ↔ ∃ C ∈ T.childrenOf c, boundedRealize φ C.sample := by
  change (Quantifier.ex.apply φ).Realize
    (freePart (n := r) (m := 0) a) (boundPart (n := r) (m := 0) a) ↔ _
  rw [eval_quantifier_step Quantifier.ex T hT φ hconst c hc a ha]
  rfl

/-- Universal EVAL over one last variable. -/
theorem eval_forall_iff_children_of_constant {r : ℕ} {T : CAD (r + 1)}
    (hT : IsCAD T) {φ : orderedRing.BoundedFormula (Fin r) 1}
    (hconst : ∀ C ∈ T.cells, ConstantOnCell φ C)
    {c : Cell r} (hc : c ∈ T.previous.cells) {a : Fin r → ℝ}
    (ha : a ∈ c.carrier) :
    Formula.Realize (∀' φ) a ↔ ∀ C ∈ T.childrenOf c, boundedRealize φ C.sample := by
  change (Quantifier.all.apply φ).Realize
    (freePart (n := r) (m := 0) a) (boundPart (n := r) (m := 0) a) ↔ _
  rw [eval_quantifier_step Quantifier.all T hT φ hconst c hc a ha]
  rfl

/-- The quantifier-step value is independent of the point in the parent cell. -/
theorem eval_quantifier_constant_on_parent {n m : ℕ} (q : Quantifier)
    (U : CAD (n + (m + 1))) (hU : IsCAD U)
    (φ : orderedRing.BoundedFormula (Fin n) (m + 1))
    (hconst : ∀ C ∈ U.cells, ConstantOnCell φ C)
    (S : Cell (n + m)) (hS : S ∈ U.previous.cells) :
    ∀ z ∈ S.carrier, ∀ w ∈ S.carrier,
      (q.apply φ).Realize (freePart z) (boundPart z) ↔
        (q.apply φ).Realize (freePart w) (boundPart w) := by
  intro z hz w hw
  rw [eval_quantifier_step q U hU φ hconst S hS z hz,
    eval_quantifier_step q U hU φ hconst S hS w hw]

end CollinsCAD
