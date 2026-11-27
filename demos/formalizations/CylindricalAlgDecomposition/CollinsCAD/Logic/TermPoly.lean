import Logic.OrderedRing

namespace FirstOrder.Language

open FirstOrder.Ring

/-- Forget the order relation from a term. -/
def forgetOrderTerm {σ : Type*} :
    orderedRing.Term σ → Language.ring.Term σ
  | .var i => .var i
  | .func f ts => .func f fun i => forgetOrderTerm (ts i)

@[simp] theorem forgetOrderTerm_onTerm {σ : Type*} (t : Language.ring.Term σ) :
    forgetOrderTerm (ringToOrderedRingLHom.onTerm t) = t := by
  induction t with
  | var => rfl
  | @func n f ts ih =>
    simp only [forgetOrderTerm, ringToOrderedRingLHom, LHom.onTerm]
    congr 1
    funext i
    exact ih i

/-- Interpret a ring term as an integer multivariate polynomial. -/
noncomputable def ringTermToMvPoly {σ : Type*}
    (t : Language.ring.Term σ) : MvPolynomial σ ℤ :=
  @Term.rec Language.ring σ
    (fun _ => MvPolynomial σ ℤ)
    (fun i => MvPolynomial.X i)
    (fun {n} f _ts ih =>
      match n, f with
      | _, FirstOrder.ringFunc.add => ih 0 + ih 1
      | _, FirstOrder.ringFunc.mul => ih 0 * ih 1
      | _, FirstOrder.ringFunc.neg => -ih 0
      | _, FirstOrder.ringFunc.zero => 0
      | _, FirstOrder.ringFunc.one => 1)
    t

@[simp] theorem ringTermToMvPoly_var {σ : Type*} (i : σ) :
    ringTermToMvPoly (Term.var i : Language.ring.Term σ) = MvPolynomial.X i := rfl

@[simp] theorem ringTermToMvPoly_add {σ : Type*}
    (ts : Fin 2 → Language.ring.Term σ) :
    ringTermToMvPoly (Term.func FirstOrder.ringFunc.add ts) =
      ringTermToMvPoly (ts 0) + ringTermToMvPoly (ts 1) := rfl

@[simp] theorem ringTermToMvPoly_mul {σ : Type*}
    (ts : Fin 2 → Language.ring.Term σ) :
    ringTermToMvPoly (Term.func FirstOrder.ringFunc.mul ts) =
      ringTermToMvPoly (ts 0) * ringTermToMvPoly (ts 1) := rfl

@[simp] theorem ringTermToMvPoly_neg {σ : Type*}
    (ts : Fin 1 → Language.ring.Term σ) :
    ringTermToMvPoly (Term.func FirstOrder.ringFunc.neg ts) =
      -ringTermToMvPoly (ts 0) := rfl

@[simp] theorem ringTermToMvPoly_zero {σ : Type*} :
    ringTermToMvPoly (Term.func FirstOrder.ringFunc.zero
      (default : Fin 0 → Language.ring.Term σ)) = 0 := rfl

@[simp] theorem ringTermToMvPoly_one {σ : Type*} :
    ringTermToMvPoly (Term.func FirstOrder.ringFunc.one
      (default : Fin 0 → Language.ring.Term σ)) = 1 := rfl

/-- Interpret an ordered-ring term as an integer multivariate polynomial. -/
noncomputable def termToMvPoly {σ : Type*} (t : orderedRing.Term σ) : MvPolynomial σ ℤ :=
  ringTermToMvPoly (forgetOrderTerm t)

/-- A ring term representing an integer multivariate polynomial. -/
noncomputable def ringTermOfMvPoly {σ : Type*}
    (P : MvPolynomial σ ℤ) : Language.ring.Term σ :=
  FirstOrder.Ring.termOfFreeCommRing
    ((freeCommRingEquivMvPolynomialInt σ).symm P)

/-- An ordered-ring term representing an integer multivariate polynomial. -/
noncomputable def mvPolyToTerm {σ : Type*}
    (P : MvPolynomial σ ℤ) : orderedRing.Term σ :=
  ringToOrderedRingLHom.onTerm (ringTermOfMvPoly P)

section RingRealization

variable {R : Type*} [CommRing R] [FirstOrder.Ring.CompatibleRing R]

/-- Ring-term translation preserves realization in any compatible ring. -/
theorem ringTermToMvPoly_realize {σ : Type*}
    (t : Language.ring.Term σ) (v : σ → R) :
    t.realize v =
      MvPolynomial.eval₂ (Int.castRingHom R) v (ringTermToMvPoly t) := by
  induction t with
  | var i =>
    rw [ringTermToMvPoly_var, MvPolynomial.eval₂_X]
    exact Term.realize_var v i
  | @func n f ts ih =>
    cases f
    · change Term.realize v
          (Term.func (FirstOrder.Ring.addFunc : Language.ring.Functions 2) ts) =
        MvPolynomial.eval₂ (Int.castRingHom R) v
          (ringTermToMvPoly (ts 0) + ringTermToMvPoly (ts 1))
      simp [Term.realize, ih, FirstOrder.Ring.CompatibleRing.funMap_add]
    · change Term.realize v
          (Term.func (FirstOrder.Ring.mulFunc : Language.ring.Functions 2) ts) =
        MvPolynomial.eval₂ (Int.castRingHom R) v
          (ringTermToMvPoly (ts 0) * ringTermToMvPoly (ts 1))
      simp [Term.realize, ih, FirstOrder.Ring.CompatibleRing.funMap_mul]
    · change Term.realize v
          (Term.func (FirstOrder.Ring.negFunc : Language.ring.Functions 1) ts) =
        MvPolynomial.eval₂ (Int.castRingHom R) v (-ringTermToMvPoly (ts 0))
      simp [Term.realize, ih, FirstOrder.Ring.CompatibleRing.funMap_neg]
    · change Term.realize v
          (Term.func (FirstOrder.Ring.zeroFunc : Language.ring.Functions 0) ts) =
        MvPolynomial.eval₂ (Int.castRingHom R) v 0
      simp [Term.realize, FirstOrder.Ring.CompatibleRing.funMap_zero]
    · change Term.realize v
          (Term.func (FirstOrder.Ring.oneFunc : Language.ring.Functions 0) ts) =
        MvPolynomial.eval₂ (Int.castRingHom R) v 1
      simp [Term.realize, FirstOrder.Ring.CompatibleRing.funMap_one]

/-- The free-commutative-ring term realizes an integer polynomial. -/
theorem ringTermOfMvPoly_realize {σ : Type*}
    (P : MvPolynomial σ ℤ) (v : σ → R) :
    (ringTermOfMvPoly P).realize v =
      MvPolynomial.eval₂ (Int.castRingHom R) v P := by
  unfold ringTermOfMvPoly
  rw [FirstOrder.Ring.realize_termOfFreeCommRing]
  let E := freeCommRingEquivMvPolynomialInt σ
  let F : FreeCommRing σ →+* R :=
    (MvPolynomial.eval₂Hom (Int.castRingHom R) v).comp E.toRingHom
  have hof : F ∘ FreeCommRing.of = v := by
    funext i
    simp [F, E, freeCommRingEquivMvPolynomialInt]
  have hlift : FreeCommRing.lift v = F := by
    rw [← FreeCommRing.lift_comp_of F, hof]
  change FreeCommRing.lift v (E.symm P) =
    MvPolynomial.eval₂ (Int.castRingHom R) v P
  rw [hlift]
  dsimp [F]
  rw [RingEquiv.apply_symm_apply]

end RingRealization

private theorem eval₂_intCast_X_eta {σ : Type*} (P : MvPolynomial σ ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom (MvPolynomial σ ℤ))
      (MvPolynomial.X : σ → MvPolynomial σ ℤ) P = P := by
  have hcast : Int.castRingHom (MvPolynomial σ ℤ) = MvPolynomial.C := by
    ext z
    simp
  rw [hcast]
  exact MvPolynomial.eval₂_eta P

/-- The polynomial round trip through the free-commutative-ring term is the
    identity. -/
theorem ringTermToMvPoly_ringTermOfMvPoly {σ : Type*}
    (P : MvPolynomial σ ℤ) :
    ringTermToMvPoly (ringTermOfMvPoly P) = P := by
  let comp : FirstOrder.Ring.CompatibleRing (MvPolynomial σ ℤ) :=
    FirstOrder.Ring.compatibleRingOfRing _
  let vX : σ → MvPolynomial σ ℤ := fun i => MvPolynomial.X i
  have hreal₁ := @ringTermToMvPoly_realize (MvPolynomial σ ℤ) _ comp σ
    (ringTermOfMvPoly P) vX
  have hreal₂ := @ringTermOfMvPoly_realize (MvPolynomial σ ℤ) _ comp σ P vX
  calc
    ringTermToMvPoly (ringTermOfMvPoly P) =
        MvPolynomial.eval₂ (Int.castRingHom (MvPolynomial σ ℤ)) vX
          (ringTermToMvPoly (ringTermOfMvPoly P)) :=
      (eval₂_intCast_X_eta _).symm
    _ = (ringTermOfMvPoly P).realize vX := hreal₁.symm
    _ = MvPolynomial.eval₂ (Int.castRingHom (MvPolynomial σ ℤ)) vX P := hreal₂
    _ = P := eval₂_intCast_X_eta P

/-- The ordered-ring polynomial round trip is the identity. -/
theorem termToMvPoly_mvPolyToTerm {σ : Type*} (P : MvPolynomial σ ℤ) :
    termToMvPoly (mvPolyToTerm P) = P := by
  change ringTermToMvPoly
    (forgetOrderTerm (ringToOrderedRingLHom.onTerm (ringTermOfMvPoly P))) = P
  rw [forgetOrderTerm_onTerm]
  exact ringTermToMvPoly_ringTermOfMvPoly P

/-- Forgetting the order preserves realization over `ℝ`. -/
theorem realize_forgetOrderTerm {σ : Type*}
    (t : orderedRing.Term σ) (v : σ → ℝ) :
    (forgetOrderTerm t).realize v = t.realize v := by
  induction t with
  | var => rfl
  | @func n f ts ih =>
    cases f <;>
      simp [forgetOrderTerm, Term.realize, ih, orderedRing_funMap_add,
        orderedRing_funMap_mul, orderedRing_funMap_neg,
        orderedRing_funMap_zero, orderedRing_funMap_one]

/-- Ordered-ring term translation preserves realization over `ℝ`. -/
theorem realize_termToMvPoly {σ : Type*}
    (t : orderedRing.Term σ) (v : σ → ℝ) :
    t.realize v =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) v (termToMvPoly t) := by
  rw [termToMvPoly, ← realize_forgetOrderTerm t v]
  exact ringTermToMvPoly_realize _ _

/-- Integer-polynomial translation preserves realization over `ℝ`. -/
theorem realize_mvPolyToTerm {σ : Type*}
    (P : MvPolynomial σ ℤ) (v : σ → ℝ) :
    (mvPolyToTerm P).realize v =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) v P := by
  have h := @LHom.realize_onTerm Language.ring orderedRing ℝ
    (inferInstance) σ (inferInstance) ringToOrderedRingLHom
    ringToOrderedRingLHom_isExpansionOn (ringTermOfMvPoly P) v
  rw [mvPolyToTerm, h]
  exact ringTermOfMvPoly_realize P v

/-- Term realization in the coefficient-map normal form used by CAD. -/
@[simp] theorem realize_termToMvPoly_intCast {σ : Type*}
    (t : orderedRing.Term σ) (v : σ → ℝ) :
    t.realize v = MvPolynomial.eval v
      (MvPolynomial.map (Int.castRingHom ℝ) (termToMvPoly t)) := by
  rw [realize_termToMvPoly, MvPolynomial.eval₂_eq_eval_map]

/-- Polynomial-term realization in the coefficient-map normal form used by CAD. -/
@[simp] theorem realize_mvPolyToTerm_intCast {σ : Type*}
    (P : MvPolynomial σ ℤ) (v : σ → ℝ) :
    (mvPolyToTerm P).realize v = MvPolynomial.eval v
      (MvPolynomial.map (Int.castRingHom ℝ) P) := by
  rw [realize_mvPolyToTerm, MvPolynomial.eval₂_eq_eval_map]

/-- Equality of terms is equality of their translated polynomials. -/
@[simp] theorem realize_equal_termToMvPoly {σ : Type*}
    (t₁ t₂ : orderedRing.Term σ) (v : σ → ℝ) :
    (t₁.equal t₂).Realize v ↔
      MvPolynomial.eval v (MvPolynomial.map (Int.castRingHom ℝ)
        (termToMvPoly t₁ - termToMvPoly t₂)) = 0 := by
  simp [Formula.realize_equal, realize_termToMvPoly_intCast, sub_eq_zero]

/-- Strict inequality of terms is negativity of their translated difference. -/
@[simp] theorem realize_lt_termToMvPoly {σ : Type*}
    (t₁ t₂ : orderedRing.Term σ) (v : σ → ℝ) :
    (orderedRingTermLtFormula t₁ t₂).Realize v ↔
      MvPolynomial.eval v (MvPolynomial.map (Int.castRingHom ℝ)
        (termToMvPoly t₁ - termToMvPoly t₂)) < 0 := by
  simp [realize_orderedRingTermLtFormula, realize_termToMvPoly_intCast]

end FirstOrder.Language
