import Logic.ElimStep

namespace CollinsCAD

open FirstOrder FirstOrder.Language Polynomial MvPolynomial

/-- Recursively eliminate a prenex prefix, using the augmented CAD at the
    full matrix arity and descending through its previous levels. -/
theorem Prefix.elim {n r o : ℕ}
    (pre : Prefix (Fin n) r o)
    (χ : orderedRing.BoundedFormula (Fin n) r) (hχ : χ.IsQF)
    (T : CAD (n + r)) (hT : IsCAD T)
    (A : Finset (MvPolynomial (Fin (n + r)) ℝ))
    (hInv : CADInvariant A T.cells)
    (hprov : HasAugmentedProvenance T A)
    (hA : IsIntPolyFamily A)
    (hsub : realAtomPolys (atomPolys χ) ⊆ A) :
    ∃ ψ : orderedRing.BoundedFormula (Fin n) o,
      ψ.IsQF ∧
      (∀ (v : Fin n → ℝ) (xs : Fin o → ℝ),
        ψ.Realize v xs ↔ (Prefix.apply pre χ).Realize v xs) ∧
      (∀ C ∈ (Prefix.dropCAD pre T).cells, ConstantOnCell ψ C) := by
  induction pre generalizing T A with
  | nil =>
    have hInv' : CADInvariant (realAtomPolys (atomPolys χ)) T.cells :=
      fun C hC => SignInvariant.mono (hInv C hC) hsub
    exact ⟨χ, hχ, fun _ _ => Iff.rfl, cellConstant_of_qf_invariant hχ hInv'⟩
  | all p ih =>
    rcases ih T hT A hInv hprov hA hsub with
      ⟨ψbody, hbodyQF, hbodyReal, hbodyConst⟩
    let U := Prefix.dropCAD p T
    have hU : IsCAD U := Prefix.dropCAD_valid p T hT
    have hprovU : HasAugmentedProvenance U (Prefix.projectFamily p A) :=
      Prefix.dropCAD_provenance p T A hprov
    rcases logic_elim_quantifier_step Quantifier.all U hU ψbody hbodyConst
        (Prefix.projectFamily (Prefix.all p) A)
        (HasAugmentedProvenance.previous hprovU)
        (Prefix.projectFamily_isIntPolyFamily (Prefix.all p) A hA) with
      ⟨ψ, hψQF, hψReal, hψConst⟩
    refine ⟨ψ, hψQF, ?_, hψConst⟩
    intro v xs
    refine (hψReal v xs).trans ?_
    simp only [Quantifier.apply, Prefix.apply, BoundedFormula.realize_all]
    exact forall_congr' (fun x => hbodyReal v (Fin.snoc xs x))
  | ex p ih =>
    rcases ih T hT A hInv hprov hA hsub with
      ⟨ψbody, hbodyQF, hbodyReal, hbodyConst⟩
    let U := Prefix.dropCAD p T
    have hU : IsCAD U := Prefix.dropCAD_valid p T hT
    have hprovU : HasAugmentedProvenance U (Prefix.projectFamily p A) :=
      Prefix.dropCAD_provenance p T A hprov
    rcases logic_elim_quantifier_step Quantifier.ex U hU ψbody hbodyConst
        (Prefix.projectFamily (Prefix.ex p) A)
        (HasAugmentedProvenance.previous hprovU)
        (Prefix.projectFamily_isIntPolyFamily (Prefix.ex p) A hA) with
      ⟨ψ, hψQF, hψReal, hψConst⟩
    refine ⟨ψ, hψQF, ?_, hψConst⟩
    intro v xs
    refine (hψReal v xs).trans ?_
    simp only [Quantifier.apply, Prefix.apply, BoundedFormula.realize_ex]
    exact exists_congr (fun x => hbodyReal v (Fin.snoc xs x))

/-- Eliminate the quantifiers of a prenex ordered-ring formula. -/
theorem logic_elim_prenex {n : ℕ} (φ : orderedRing.Formula (Fin n))
    (hφ : φ.IsPrenex) :
    ∃ ψ : orderedRing.Formula (Fin n),
      ψ.IsQF ∧ ∀ v : Fin n → ℝ, φ.Realize v ↔ ψ.Realize v := by
  rcases PrenexView.exists hφ with ⟨r, pre, χ, hχ, heq⟩
  let A := realAtomPolys (atomPolys χ)
  rcases exists_augmented_cad (n + r) A with ⟨T, hT, hInv, hprov⟩
  have hA : IsIntPolyFamily A := isIntPolyFamily_realAtomPolys (atomPolys χ)
  rcases Prefix.elim pre χ hχ T hT A hInv hprov hA (fun _ h => h) with
    ⟨ψ, hψQF, hψReal, _⟩
  refine ⟨ψ, hψQF, ?_⟩
  intro v
  have hb := hψReal v (default : Fin 0 → ℝ)
  rw [Formula.boundedFormula_realize_eq_realize,
    Formula.boundedFormula_realize_eq_realize, heq] at hb
  exact hb.symm

/-- Every ordered-ring formula over the reals has an equivalent
    quantifier-free formula. -/
theorem rcf_quantifier_elimination {n : ℕ} (φ : orderedRing.Formula (Fin n)) :
    ∃ ψ : orderedRing.Formula (Fin n),
      ψ.IsQF ∧ ∀ v : Fin n → ℝ, φ.Realize v ↔ ψ.Realize v := by
  rcases logic_elim_prenex φ.toPrenex φ.toPrenex_isPrenex with
    ⟨ψ, hψQF, hψ⟩
  refine ⟨ψ, hψQF, fun v => ?_⟩
  have hp := BoundedFormula.realize_toPrenex (φ := φ) (v := v)
    (xs := (default : Fin 0 → ℝ))
  rw [Formula.boundedFormula_realize_eq_realize,
    Formula.boundedFormula_realize_eq_realize] at hp
  exact hp.symm.trans (hψ v)

/-- Quantifier elimination for formulas over any finite variable type. -/
theorem rcf_quantifier_elimination_fintype {α : Type*} [Fintype α]
    (φ : orderedRing.Formula α) :
    ∃ ψ : orderedRing.Formula α,
      ψ.IsQF ∧ ∀ v : α → ℝ, φ.Realize v ↔ ψ.Realize v := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  rcases rcf_quantifier_elimination (φ.relabel e) with
    ⟨ψ, hψQF, hψ⟩
  refine ⟨ψ.relabel e.symm,
    BoundedFormula.IsQF.relabel hψQF (Sum.inl ∘ e.symm), ?_⟩
  intro v
  have hcomp : (v ∘ e.symm) ∘ e = v := by
    funext a
    simp
  calc
    φ.Realize v ↔ (φ.relabel e).Realize (v ∘ e.symm) := by
      rw [Formula.realize_relabel, hcomp]
    _ ↔ ψ.Realize (v ∘ e.symm) := hψ (v ∘ e.symm)
    _ ↔ (ψ.relabel e.symm).Realize v := by
      rw [Formula.realize_relabel]

/-- Quantifier elimination for ordered-ring sentences. -/
theorem rcf_sentence_quantifier_elimination (φ : orderedRing.Sentence) :
    ∃ ψ : orderedRing.Sentence,
      ψ.IsQF ∧ (Sentence.Realize (L := orderedRing) (M := ℝ) φ ↔
        Sentence.Realize (L := orderedRing) (M := ℝ) ψ) := by
  rcases rcf_quantifier_elimination_fintype φ with ⟨ψ, hψQF, hψ⟩
  refine ⟨ψ, hψQF, ?_⟩
  simpa only [Sentence.Realize] using
    hψ (@default (Empty → ℝ) Unique.instInhabited)

/-- Blueprint name for the main real-closed-field quantifier-elimination
    theorem. -/
theorem logic_elim_main {n : ℕ} (φ : orderedRing.Formula (Fin n)) :
    ∃ ψ : orderedRing.Formula (Fin n),
      ψ.IsQF ∧ ∀ v : Fin n → ℝ, φ.Realize v ↔ ψ.Realize v :=
  rcf_quantifier_elimination φ

end CollinsCAD
