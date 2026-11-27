import Logic.Prefix
import Logic.SignFormula
import CAD.Define

namespace CollinsCAD

open FirstOrder FirstOrder.Language Polynomial MvPolynomial

/-- One ELIM step replaces a quantified formula by the finite disjunction of
    DEFINE formulas for accepting parent cells. -/
theorem logic_elim_quantifier_step {n m : ℕ} (q : Quantifier)
    (U : CAD (n + (m + 1))) (hU : IsCAD U)
    (φ : orderedRing.BoundedFormula (Fin n) (m + 1))
    (hconst : ∀ C ∈ U.cells, ConstantOnCell φ C)
    (B : Finset (MvPolynomial (Fin (n + m)) ℝ))
    (hprov : HasAugmentedProvenance U.previous B)
    (hB : IsIntPolyFamily B) :
    ∃ ψ : orderedRing.BoundedFormula (Fin n) m,
      ψ.IsQF ∧
      (∀ (v : Fin n → ℝ) (xs : Fin m → ℝ),
        ψ.Realize v xs ↔ (q.apply φ).Realize v xs) ∧
      (∀ C ∈ U.previous.cells, ConstantOnCell ψ C) := by
  classical
  let cells := {S : Cell (n + m) // S ∈ U.previous.cells}
  let mark : Cell (n + m) → Prop := fun S =>
    q.fold (fun C => boundedRealize φ C.sample) (U.childrenOf S)
  let accept : Finset cells := Finset.univ.filter (fun S => mark S.1)
  have hdefs : ∀ S : cells, ∃ F : SignFormula (n + m),
      (∀ x, F.Holds x ↔ x ∈ S.1.carrier) ∧
      F.Holds S.1.sample ∧ F.polys ⊆ definePolys (n + m) B := by
    intro S
    exact cad_define_cell_formula (n + m) B U.previous hprov S.1 S.2
  choose F hdef _hsample hsupport using hdefs
  have hFint : ∀ S : cells, ∀ Q ∈ (F S).polys, IsIntPoly Q := by
    intro S Q hQ
    exact isIntPoly_of_mem_definePolys (n + m) B hB Q (hsupport S hQ)
  let θ : accept → orderedRing.BoundedFormula (Fin n) m := fun c =>
    signFormulaToBounded (F c.1) (hFint c.1)
  let ψ := BoundedFormula.iSup θ
  have hψ (v : Fin n → ℝ) (xs : Fin m → ℝ) :
      ψ.Realize v xs ↔
        ∃ S : cells, S ∈ accept ∧ joinTuple v xs ∈ S.1.carrier := by
    change (BoundedFormula.iSup θ).Realize v xs ↔ _
    rw [BoundedFormula.realize_iSup]
    constructor
    · rintro ⟨c, hc⟩
      have hc' : (θ c).Realize v xs ↔ joinTuple v xs ∈ c.1.1.carrier := by
        dsimp only [θ]
        rw [realize_signFormulaToBounded]
        exact hdef c.1 (joinTuple v xs)
      exact ⟨c.1, c.2, hc'.mp hc⟩
    · rintro ⟨S, hS, hzS⟩
      let c : accept := ⟨S, hS⟩
      have hc' : (θ c).Realize v xs ↔ joinTuple v xs ∈ c.1.1.carrier := by
        dsimp only [θ]
        rw [realize_signFormulaToBounded]
        exact hdef c.1 (joinTuple v xs)
      exact ⟨c, hc'.mpr hzS⟩
  refine ⟨ψ, ?_, ?_, ?_⟩
  · apply isQF_iSup
    intro c
    exact signFormulaToBounded_isQF (F c.1) (hFint c.1)
  · intro v xs
    rcases U.previous.decomposition.cover (joinTuple v xs) with ⟨S, hS, hzS⟩
    let S₀ : cells := ⟨S, hS⟩
    have hstep := eval_quantifier_step q U hU φ hconst S hS
      (joinTuple v xs) hzS
    simp only [freePart_joinTuple, boundPart_joinTuple] at hstep
    have hmem : (∃ T : cells, T ∈ accept ∧ joinTuple v xs ∈ T.1.carrier) ↔
        mark S := by
      constructor
      · rintro ⟨T, hTacc, hzT⟩
        have hTmark : mark T.1 := (Finset.mem_filter.mp hTacc).2
        have heq : T.1 = S := by
          by_contra hne
          exact Set.disjoint_left.mp
            (U.previous.decomposition.pairwise_disjoint T.1 T.2 S hS hne) hzT hzS
        simpa [heq] using hTmark
      · intro hmark
        have hacc : S₀ ∈ accept := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmark⟩
        exact ⟨S₀, hacc, hzS⟩
    rw [hψ, hmem]
    exact hstep.symm
  · intro C hC
    have hcell (x : Fin (n + m) → ℝ) (hx : x ∈ C.carrier) :
        ψ.Realize (freePart x) (boundPart x) ↔ mark C := by
      rw [hψ]
      simp only [joinTuple_freePart_boundPart]
      constructor
      · rintro ⟨T, hTacc, hxT⟩
        have hTmark : mark T.1 := (Finset.mem_filter.mp hTacc).2
        have heq : T.1 = C := by
          by_contra hne
          exact Set.disjoint_left.mp
            (U.previous.decomposition.pairwise_disjoint T.1 T.2 C hC hne) hxT hx
        simpa [heq] using hTmark
      · intro hmark
        let Csub : cells := ⟨C, hC⟩
        have hacc : Csub ∈ accept :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmark⟩
        exact ⟨Csub, hacc, hx⟩
    change ∀ z ∈ C.carrier, boundedRealize ψ z ↔ boundedRealize ψ C.sample
    intro z hz
    exact (hcell z hz).trans (hcell C.sample C.sample_mem).symm

end CollinsCAD
