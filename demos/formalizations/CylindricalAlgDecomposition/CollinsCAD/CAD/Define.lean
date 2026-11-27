import Mathlib
import CAD.AugmentedDecomp
import CAD.SignFormula

/-!
# DEFINE cell formulas

Each lifted cell is characterized by its parent's sign conditions together
with the sign vector of the local augmented polynomial family at the child
sample. Fixed-fibre sign-vector uniqueness ensures that these conditions
select exactly the intended sector or section.
-/

namespace CollinsCAD

open Polynomial MvPolynomial

/-- Define one lifted child from its parent formula and local augmented
    family. -/
theorem define_lifted_cell_formula {r : ℕ}
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {previous : CAD r} {next : Decomposition (r + 1)} {edges : List (Cylinder r)}
    (hmap : IsParentChildMap previous.decomposition next edges)
    (haug : ∀ L ∈ edges, IsAugmentedCylinder A L)
    (L : Cylinder r) (hL : L ∈ edges) (C : Cell (r + 1)) (hC : C ∈ L.children)
    (Fparent : SignFormula r)
    (hparentDef : ∀ x, Fparent.Holds x ↔ x ∈ L.parent.carrier)
    (hparentSample : Fparent.Holds L.parent.sample)
    (hparentSupport : Fparent.polys ⊆ definePolys r (augProj A)) :
    ∃ F : SignFormula (r + 1),
      (∀ x, F.Holds x ↔ x ∈ C.carrier) ∧
      F.Holds C.sample ∧ F.polys ⊆ definePolys (r + 1) A := by
  classical
  have hpartL : IsCylinderPartition L := hmap.2.2.2.2.2 L hL
  have haugL : IsAugmentedCylinder A L := haug L hL
  let F := Fparent.prefix.union (signFormulaOfSample L.family C.sample)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro z
    constructor
    · intro hF
      rw [SignFormula.union_holds] at hF
      have hzparent : Fin.init z ∈ L.parent.carrier :=
        (hparentDef (Fin.init z)).mp
          ((SignFormula.prefix_holds_init Fparent z).mp hF.1)
      let a := Fin.init z
      let x := z (Fin.last r)
      have hzsnoc : z = Fin.snoc a x := (Fin.snoc_init_self z).symm
      rcases hpartL.1 a hzparent x with ⟨d, hd, hzd⟩
      have hsign : ∀ Q ∈ L.family,
          SignType.sign (Polynomial.eval x (fiberPoly r Q a)) =
            SignType.sign (Polynomial.eval (C.sample (Fin.last r))
              (fiberPoly r Q (Fin.init C.sample))) := by
        intro Q hQ
        have hcond := (signFormulaOfSample_holds L.family C.sample z).mp hF.2 Q hQ
        have hzEval : MvPolynomial.eval z Q =
            Polynomial.eval x (fiberPoly r Q a) := by
          calc
            MvPolynomial.eval z Q = MvPolynomial.eval (Fin.snoc a x) Q := by rw [hzsnoc]
            _ = Polynomial.eval x (fiberPoly r Q a) :=
              (fiberPoly_eval r Q a x).symm
        have hsEval : MvPolynomial.eval C.sample Q =
            Polynomial.eval (C.sample (Fin.last r))
              (fiberPoly r Q (Fin.init C.sample)) := by
          calc
            MvPolynomial.eval C.sample Q =
                MvPolynomial.eval (Fin.snoc (Fin.init C.sample)
                  (C.sample (Fin.last r))) Q := by rw [Fin.snoc_init_self]
            _ = Polynomial.eval (C.sample (Fin.last r))
                (fiberPoly r Q (Fin.init C.sample)) :=
              (fiberPoly_eval r Q (Fin.init C.sample) (C.sample (Fin.last r))).symm
        rw [hzEval, hsEval] at hcond
        exact hcond
      rcases hpartL.2.1 a hzparent C hC with ⟨xc, hxc⟩
      have hCd : C = d := by
        apply Cylinder.child_eq_of_signVector_eq L hpartL
          haugL.2.1 haugL.2.2.1 hC hd hzparent hxc hzd
        intro Q hQ
        have hCsnoc : Fin.snoc (Fin.init C.sample) (C.sample (Fin.last r)) =
            C.sample := Fin.snoc_init_self C.sample
        exact (Cylinder.sign_fiber_eq_of_snoc_mem_general L hC hQ hxc
          (by rw [hCsnoc]; exact C.sample_mem)).trans (hsign Q hQ).symm
      subst d
      simpa [hzsnoc] using hzd
    · intro hz
      rw [SignFormula.union_holds]
      refine ⟨?_, ?_⟩
      · rw [SignFormula.prefix_holds_init Fparent]
        exact (hparentDef (Fin.init z)).mpr
          (LiftShape.init_mem (L.children_shape C hC) hz)
      · apply (signFormulaOfSample_holds L.family C.sample z).mpr
        intro Q hQ
        rcases L.invariant C hC Q hQ with ⟨s, hs⟩
        exact (hs z hz).trans (hs C.sample C.sample_mem).symm
  · rw [SignFormula.union_holds]
    constructor
    · rw [SignFormula.prefix_holds_init Fparent]
      have hinit := hpartL.2.2.2.2 C hC
      rw [hinit]
      exact hparentSample
    · apply (signFormulaOfSample_holds L.family C.sample C.sample).mpr
      intro Q hQ
      rfl
  · rw [SignFormula.polys_union, SignFormula.polys_prefix,
      SignFormula.polys_signFormulaOfSample]
    intro Q hQ
    rcases Finset.mem_union.mp hQ with hpre | hfam
    · rcases Finset.mem_image.mp hpre with ⟨R, hR, rfl⟩
      exact mem_definePolys_succ.mpr (Or.inl ⟨R, hparentSupport hR, rfl⟩)
    · exact mem_definePolys_succ.mpr (Or.inr (haugL.1 hfam))

/-- Every cell of an augmented CAD is defined by a finite conjunction of
    polynomial sign conditions from the DEFINE support envelope. -/
theorem cad_define_cell_formula (r : ℕ) :
    ∀ (A : Finset (MvPolynomial (Fin r) ℝ)) (T : CAD r),
      HasAugmentedProvenance T A → ∀ C ∈ T.cells,
        ∃ F : SignFormula r,
          (∀ x, F.Holds x ↔ x ∈ C.carrier) ∧
          F.Holds C.sample ∧ F.polys ⊆ definePolys r A := by
  induction r with
  | zero =>
    intro A T hprov C _hC
    let F : SignFormula 0 := ⟨∅⟩
    have hcarrier : C.carrier = Set.univ := by
      ext x
      constructor
      · intro _
        exact Set.mem_univ x
      · intro _
        have hx : x = C.sample := Subsingleton.elim _ _
        simpa [hx] using C.sample_mem
    refine ⟨F, ?_, ?_, ?_⟩
    · intro x
      rw [hcarrier]
      constructor
      · intro _
        exact Set.mem_univ x
      · intro _ c hc
        cases hc
    · intro c hc
      cases hc
    · intro Q hQ
      change Q ∈ (∅ : Finset (MvPolynomial (Fin 0) ℝ)) at hQ
      cases hQ
  | succ r ih =>
    intro A T hprov C hC
    cases T with
    | succ previous next edges =>
      rcases hprov with ⟨hprovPrev, hmap, haug⟩
      have hCflat : C ∈ edges.flatMap (fun L => L.children) := by
        rw [← hmap.2.2.2.2.1]
        exact hC
      rcases List.mem_flatMap.mp hCflat with ⟨L, hL, hCL⟩
      rcases ih (augProj A) previous hprovPrev L.parent (hmap.2.1 L hL) with
        ⟨Fparent, hparentDef, hparentSample, hparentSupport⟩
      exact define_lifted_cell_formula hmap haug L hL C hCL Fparent
        hparentDef hparentSample hparentSupport

/-- Collins' DEFINE existence theorem. -/
theorem cad_define_exists (r : ℕ) (A : Finset (MvPolynomial (Fin r) ℝ)) :
    ∃ T : CAD r, IsCAD T ∧ CADInvariant A T.cells ∧
      HasAugmentedProvenance T A ∧ ∀ C ∈ T.cells,
        ∃ F : SignFormula r,
          (∀ x, F.Holds x ↔ x ∈ C.carrier) ∧
          F.Holds C.sample ∧ F.polys ⊆ definePolys r A := by
  rcases exists_augmented_cad r A with ⟨T, hT, hinv, hprov⟩
  exact ⟨T, hT, hinv, hprov, cad_define_cell_formula r A T hprov⟩

end CollinsCAD
