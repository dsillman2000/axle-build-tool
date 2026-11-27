import Logic.Basic

/-!
# First-order ordered-ring language

The language extends the ring function symbols with one primitive binary
strict-order relation. Ordered-ring terms translate structurally to integer
multivariate polynomials, while the reverse translation uses Mathlib's free
commutative ring representation. Both directions preserve realization on the
real ordered-ring structure.
-/

open scoped FirstOrder.Language

namespace FirstOrder.Language

open Structure

/-- The sole non-logical relation symbol of the ordered-ring language. -/
inductive orderedRingRel : ℕ → Type
  | lt : orderedRingRel 2
  deriving DecidableEq

/-- The language of ordered rings: the ring function symbols together with a
    primitive binary strict-order relation. -/
def orderedRing : Language where
  Functions := Language.ring.Functions
  Relations := orderedRingRel

/-- The strict-order relation symbol. -/
abbrev ltSymb : orderedRing.Relations 2 := orderedRingRel.lt

/-- Ring function symbols viewed in the ordered-ring language. -/
abbrev addFunc : orderedRing.Functions 2 := FirstOrder.Ring.addFunc
abbrev mulFunc : orderedRing.Functions 2 := FirstOrder.Ring.mulFunc
abbrev negFunc : orderedRing.Functions 1 := FirstOrder.Ring.negFunc
abbrev zeroFunc : orderedRing.Functions 0 := FirstOrder.Ring.zeroFunc
abbrev oneFunc : orderedRing.Functions 0 := FirstOrder.Ring.oneFunc

instance : IsEmpty (orderedRing.Relations 0) :=
  ⟨fun R => by cases R⟩

instance : IsEmpty (orderedRing.Relations 1) :=
  ⟨fun R => by cases R⟩

instance : Subsingleton (orderedRing.Relations 2) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

/-- The canonical ordered-ring structure on `ℝ`. -/
instance orderedRingStructure : orderedRing.Structure ℝ where
  funMap := fun {n} f =>
    match n, f with
    | _, FirstOrder.ringFunc.add => fun x => x 0 + x 1
    | _, FirstOrder.ringFunc.mul => fun x => x 0 * x 1
    | _, FirstOrder.ringFunc.neg => fun x => -x 0
    | _, FirstOrder.ringFunc.zero => fun _ => 0
    | _, FirstOrder.ringFunc.one => fun _ => 1
  RelMap := fun {n} R =>
    match n, R with
    | _, orderedRingRel.lt => fun x => x 0 < x 1

@[simp] theorem orderedRing_funMap_add (x : Fin 2 → ℝ) :
    @Structure.funMap orderedRing ℝ _ 2 addFunc x = x 0 + x 1 := rfl

@[simp] theorem orderedRing_funMap_mul (x : Fin 2 → ℝ) :
    @Structure.funMap orderedRing ℝ _ 2 mulFunc x = x 0 * x 1 := rfl

@[simp] theorem orderedRing_funMap_neg (x : Fin 1 → ℝ) :
    @Structure.funMap orderedRing ℝ _ 1 negFunc x = -x 0 := rfl

@[simp] theorem orderedRing_funMap_zero (x : Fin 0 → ℝ) :
    @Structure.funMap orderedRing ℝ _ 0 zeroFunc x = 0 := rfl

@[simp] theorem orderedRing_funMap_one (x : Fin 0 → ℝ) :
    @Structure.funMap orderedRing ℝ _ 0 oneFunc x = 1 := rfl

@[simp] theorem orderedRing_relMap_lt (x : Fin 2 → ℝ) :
    @Structure.RelMap orderedRing ℝ _ 2 ltSymb x = (x 0 < x 1) := rfl

/-- Public ring-style term-building API. The current DEFINE translation only
    needs zero, but the full operation set and realization lemmas make the
    ordered-ring language convenient for downstream examples and clients. -/
instance (α : Type*) : Zero (orderedRing.Term α) :=
  ⟨Constants.term zeroFunc⟩

instance (α : Type*) : One (orderedRing.Term α) :=
  ⟨Constants.term oneFunc⟩

instance (α : Type*) : Add (orderedRing.Term α) :=
  ⟨fun t₁ t₂ => addFunc.apply₂ t₁ t₂⟩

instance (α : Type*) : Mul (orderedRing.Term α) :=
  ⟨fun t₁ t₂ => mulFunc.apply₂ t₁ t₂⟩

instance (α : Type*) : Neg (orderedRing.Term α) :=
  ⟨fun t => negFunc.apply₁ t⟩

instance orderedRingTermOfNatZero (α : Type*) : OfNat (orderedRing.Term α) 0 :=
  ⟨Constants.term zeroFunc⟩

instance orderedRingTermOfNatOne (α : Type*) : OfNat (orderedRing.Term α) 1 :=
  ⟨Constants.term oneFunc⟩

@[simp] theorem zero_def (α : Type*) :
    (0 : orderedRing.Term α) = Constants.term zeroFunc := rfl

@[simp] theorem one_def (α : Type*) :
    (1 : orderedRing.Term α) = Constants.term oneFunc := rfl

@[simp] theorem add_def (α : Type*) (t₁ t₂ : orderedRing.Term α) :
    t₁ + t₂ = addFunc.apply₂ t₁ t₂ := rfl

@[simp] theorem mul_def (α : Type*) (t₁ t₂ : orderedRing.Term α) :
    t₁ * t₂ = mulFunc.apply₂ t₁ t₂ := rfl

@[simp] theorem neg_def (α : Type*) (t : orderedRing.Term α) :
    -t = negFunc.apply₁ t := rfl

@[simp] theorem realize_zero (α : Type*) (v : α → ℝ) :
    Term.realize v (0 : orderedRing.Term α) = 0 := by
  simp only [zero_def, Term.realize_constants, constantMap]
  exact orderedRing_funMap_zero _

@[simp] theorem realize_one (α : Type*) (v : α → ℝ) :
    Term.realize v (1 : orderedRing.Term α) = 1 := by
  simp only [one_def, Term.realize_constants, constantMap]
  exact orderedRing_funMap_one _

@[simp] theorem realize_add (α : Type*) (t₁ t₂ : orderedRing.Term α) (v : α → ℝ) :
    Term.realize v (t₁ + t₂) = Term.realize v t₁ + Term.realize v t₂ := by
  simp [add_def]

@[simp] theorem realize_mul (α : Type*) (t₁ t₂ : orderedRing.Term α) (v : α → ℝ) :
    Term.realize v (t₁ * t₂) = Term.realize v t₁ * Term.realize v t₂ := by
  simp [mul_def]

@[simp] theorem realize_neg (α : Type*) (t : orderedRing.Term α) (v : α → ℝ) :
    Term.realize v (-t) = -Term.realize v t := by
  simp [neg_def]

/-- The canonical ring-language structure on `ℝ`, enabled explicitly by
    opening the `FirstOrder.Language` scope. -/
scoped instance compatibleRingReal : FirstOrder.Ring.CompatibleRing ℝ :=
  FirstOrder.Ring.compatibleRingOfRing ℝ

/-- The inclusion of the ring language into the ordered-ring language. -/
def ringToOrderedRingLHom : Language.ring →ᴸ orderedRing where
  onFunction := fun {_n} f => f
  onRelation := fun {_n} R => isEmptyElim R

/-- The ring inclusion is an expansion on `ℝ`. -/
instance ringToOrderedRingLHom_isExpansionOn :
    ringToOrderedRingLHom.IsExpansionOn ℝ where
  map_onFunction := fun _ _ => rfl
  map_onRelation := fun R => isEmptyElim R

/-- Primitive strict inequality on bounded terms. -/
def orderedRingTermLt {α : Type*} {n : ℕ}
    (t₁ t₂ : orderedRing.Term (α ⊕ (Fin n))) :
    orderedRing.BoundedFormula α n :=
  ltSymb.boundedFormula₂ t₁ t₂

/-- Primitive strict inequality on free-variable terms. -/
def orderedRingTermLtFormula {α : Type*}
    (t₁ t₂ : orderedRing.Term α) : orderedRing.Formula α :=
  ltSymb.formula₂ t₁ t₂

@[simp] theorem realize_orderedRingTermLt {α : Type*} {n : ℕ}
    {t₁ t₂ : orderedRing.Term (α ⊕ (Fin n))} {v : α → ℝ} {xs : Fin n → ℝ} :
    (orderedRingTermLt t₁ t₂).Realize v xs ↔
      t₁.realize (Sum.elim v xs) < t₂.realize (Sum.elim v xs) := by
  simp [orderedRingTermLt, BoundedFormula.realize_rel₂, orderedRing_relMap_lt]

@[simp] theorem realize_orderedRingTermLtFormula {α : Type*}
    {t₁ t₂ : orderedRing.Term α} {v : α → ℝ} :
    (orderedRingTermLtFormula t₁ t₂).Realize v ↔
      t₁.realize v < t₂.realize v := by
  simp [orderedRingTermLtFormula, Formula.realize_rel₂, orderedRing_relMap_lt]

end FirstOrder.Language
