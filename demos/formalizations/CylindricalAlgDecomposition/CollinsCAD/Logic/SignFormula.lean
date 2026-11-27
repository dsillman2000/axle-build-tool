import Logic.AtomPolys
import CAD.SignFormula

namespace CollinsCAD

open FirstOrder FirstOrder.Language Polynomial MvPolynomial

/-- Choose the integer polynomial underlying an integral real polynomial. -/
noncomputable def intPolyTerm {r : ℕ} {P : MvPolynomial (Fin r) ℝ}
    (hP : IsIntPoly P) : orderedRing.Term (Fin r) :=
  mvPolyToTerm (Classical.choose hP)

/-- The chosen integer polynomial term realizes the given real polynomial. -/
@[simp] theorem realize_intPolyTerm {r : ℕ} {P : MvPolynomial (Fin r) ℝ}
    (hP : IsIntPoly P) (z : Fin r → ℝ) :
    (intPolyTerm hP).realize z = MvPolynomial.eval z P := by
  calc
    (intPolyTerm hP).realize z =
        MvPolynomial.eval z (intCastMv r (Classical.choose hP)) :=
      realize_mvPolyToTerm_intCast _ z
    _ = MvPolynomial.eval z P := by
      exact congrArg (MvPolynomial.eval z) (Classical.choose_spec hP).symm

/-- Translate one integral sign condition into ordered-ring syntax. -/
noncomputable def signConditionToFormula {r : ℕ} (c : SignCondition r)
    (hc : IsIntPoly c.poly) : orderedRing.Formula (Fin r) :=
  match c.sign with
  | 0 => (intPolyTerm hc).equal (zeroTerm : orderedRing.Term (Fin r))
  | -1 => orderedRingTermLtFormula (intPolyTerm hc) (zeroTerm : orderedRing.Term (Fin r))
  | 1 => orderedRingTermLtFormula (zeroTerm : orderedRing.Term (Fin r)) (intPolyTerm hc)

/-- Sign-condition translation preserves truth. -/
@[simp] theorem realize_signConditionToFormula {r : ℕ} (c : SignCondition r)
    (hc : IsIntPoly c.poly) (z : Fin r → ℝ) :
    (signConditionToFormula c hc).Realize z ↔ c.Holds z := by
  rcases c with ⟨P, s⟩
  cases s
  · change ((intPolyTerm hc).equal (zeroTerm : orderedRing.Term (Fin r))).Realize z ↔
      SignType.sign (MvPolynomial.eval z P) = 0
    rw [Formula.realize_equal, realize_intPolyTerm, realize_zeroTerm]
    exact sign_eq_zero_iff.symm
  · change (orderedRingTermLtFormula (intPolyTerm hc)
      (zeroTerm : orderedRing.Term (Fin r))).Realize z ↔
      SignType.sign (MvPolynomial.eval z P) = -1
    rw [realize_orderedRingTermLtFormula, realize_intPolyTerm, realize_zeroTerm]
    exact sign_eq_neg_one_iff.symm
  · change (orderedRingTermLtFormula (zeroTerm : orderedRing.Term (Fin r))
      (intPolyTerm hc)).Realize z ↔ SignType.sign (MvPolynomial.eval z P) = 1
    rw [realize_orderedRingTermLtFormula, realize_intPolyTerm, realize_zeroTerm]
    exact sign_eq_one_iff.symm

/-- Sign-condition translation is quantifier-free. -/
theorem signConditionToFormula_isQF {r : ℕ} (c : SignCondition r)
    (hc : IsIntPoly c.poly) : (signConditionToFormula c hc).IsQF := by
  rcases c with ⟨P, s⟩
  cases s
  · exact BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.equal _ _)
  · exact BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.rel _ _)
  · exact BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.rel _ _)

/-- Finite conjunctions of quantifier-free bounded formulas are
    quantifier-free. -/
theorem isQF_iInf {α : Type*} [Finite β] {n : ℕ}
    (f : β → orderedRing.BoundedFormula α n) (hf : ∀ b, (f b).IsQF) :
    (BoundedFormula.iInf f).IsQF := by
  classical
  let fintype : Fintype β := Fintype.ofFinite β
  have aux : ∀ l : List β, (∀ b ∈ l, (f b).IsQF) →
      BoundedFormula.IsQF ((l.map f).foldr (· ⊓ ·) ⊤) := by
    intro l
    induction l with
    | nil => intro _; exact BoundedFormula.IsQF.top
    | cons b bs ih =>
      intro hl
      simp only [List.map_cons, List.foldr_cons]
      exact (hl b (by simp)).inf
        (ih (fun c hc => hl c (by simp [hc])))
  unfold BoundedFormula.iInf
  dsimp only
  exact aux ((@Finset.univ β fintype).toList)
    (fun b hb => hf b)

/-- Finite disjunctions of quantifier-free bounded formulas are
    quantifier-free. -/
theorem isQF_iSup {α : Type*} [Finite β] {n : ℕ}
    (f : β → orderedRing.BoundedFormula α n) (hf : ∀ b, (f b).IsQF) :
    (BoundedFormula.iSup f).IsQF := by
  classical
  let fintype : Fintype β := Fintype.ofFinite β
  have aux : ∀ l : List β, (∀ b ∈ l, (f b).IsQF) →
      BoundedFormula.IsQF ((l.map f).foldr (· ⊔ ·) ⊥) := by
    intro l
    induction l with
    | nil => intro _; exact BoundedFormula.isQF_bot
    | cons b bs ih =>
      intro hl
      simp only [List.map_cons, List.foldr_cons]
      exact (hl b (by simp)).sup
        (ih (fun c hc => hl c (by simp [hc])))
  unfold BoundedFormula.iSup
  dsimp only
  exact aux ((@Finset.univ β fintype).toList)
    (fun b hb => hf b)

/-- Translate an integral sign formula into a finite ordered-ring
    conjunction. -/
noncomputable def signFormulaToFormula {r : ℕ} (F : SignFormula r)
    (hF : ∀ Q ∈ F.polys, IsIntPoly Q) : orderedRing.Formula (Fin r) :=
  Formula.iInf (fun c : F.conditions =>
    signConditionToFormula c.1 (hF c.1.poly (Finset.mem_image.mpr ⟨c.1, c.2, rfl⟩)))

/-- Sign-formula translation is quantifier-free. -/
theorem signFormulaToFormula_isQF {r : ℕ} (F : SignFormula r)
    (hF : ∀ Q ∈ F.polys, IsIntPoly Q) : (signFormulaToFormula F hF).IsQF := by
  unfold signFormulaToFormula
  apply isQF_iInf
  intro c
  exact signConditionToFormula_isQF c.1
    (hF c.1.poly (Finset.mem_image.mpr ⟨c.1, c.2, rfl⟩))

/-- Sign-formula translation preserves truth. -/
@[simp] theorem realize_signFormulaToFormula {r : ℕ} (F : SignFormula r)
    (hF : ∀ Q ∈ F.polys, IsIntPoly Q) (z : Fin r → ℝ) :
    (signFormulaToFormula F hF).Realize z ↔ F.Holds z := by
  classical
  rw [signFormulaToFormula, Formula.realize_iInf]
  constructor
  · intro h c hc
    exact (realize_signConditionToFormula c
      (hF c.poly (Finset.mem_image.mpr ⟨c, hc, rfl⟩)) z).mp (h ⟨c, hc⟩)
  · intro h c
    exact (realize_signConditionToFormula c.1
      (hF c.1.poly (Finset.mem_image.mpr ⟨c.1, c.2, rfl⟩)) z).mpr
      (h c.1 c.2)

/-- View a sign formula in CAD coordinates as a bounded formula. -/
noncomputable def signFormulaToBounded {n m : ℕ} (F : SignFormula (n + m))
    (hF : ∀ Q ∈ F.polys, IsIntPoly Q) :
    orderedRing.BoundedFormula (Fin n) m :=
  BoundedFormula.relabel (finSumFinEquiv (m := n) (n := m)).symm
    (signFormulaToFormula F hF)

/-- Bounded sign-formula translation is quantifier-free. -/
theorem signFormulaToBounded_isQF {n m : ℕ} (F : SignFormula (n + m))
    (hF : ∀ Q ∈ F.polys, IsIntPoly Q) :
    (signFormulaToBounded F hF).IsQF := by
  unfold signFormulaToBounded
  apply BoundedFormula.IsQF.relabel
  exact signFormulaToFormula_isQF F hF

/-- Bounded sign-formula translation preserves truth on joined tuples. -/
@[simp] theorem realize_signFormulaToBounded {n m : ℕ} (F : SignFormula (n + m))
    (hF : ∀ Q ∈ F.polys, IsIntPoly Q) (v : Fin n → ℝ) (xs : Fin m → ℝ) :
    (signFormulaToBounded F hF).Realize v xs ↔ F.Holds (joinTuple v xs) := by
  rw [signFormulaToBounded, BoundedFormula.realize_relabel,
    Formula.boundedFormula_realize_eq_realize, realize_signFormulaToFormula]
  have harg : (Sum.elim v (xs ∘ Fin.castAdd 0) ∘
      (finSumFinEquiv (m := n) (n := m)).symm) = joinTuple v xs := by
    funext i
    rcases (finSumFinEquiv (m := n) (n := m)).symm i with j | j <;>
      simp [joinTuple, finSumFinEquiv]
  rw [harg]

end CollinsCAD
