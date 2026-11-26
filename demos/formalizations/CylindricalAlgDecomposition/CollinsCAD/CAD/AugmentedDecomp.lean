import Mathlib
import CAD.Decomp
import CAD.AugmentedProjection
import CAD.LiftSignVector

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- A cylinder carrying the local augmented family and its derivative
    dichotomy. -/
def IsAugmentedCylinder (A : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (L : Cylinder r) : Prop :=
  L.family ⊆ augPolySet A ∧
  (∀ Q ∈ L.family, ∀ a ∈ L.parent.carrier, fiberPoly r Q a ≠ 0) ∧
  (∀ Q ∈ L.family, ∀ D ∈ derivativeTower (finLastEquiv ℝ r Q),
    (finLastEquiv ℝ r).symm D ∈ L.family ∨
      ∀ a ∈ L.parent.carrier, fiberPoly r ((finLastEquiv ℝ r).symm D) a = 0) ∧
  (∀ P ∈ A, P ∈ L.family ∨
    ∀ a ∈ L.parent.carrier, fiberPoly r P a = 0)

/-- An augmented cylinder is invariant for the original input family. -/
theorem IsAugmentedCylinder.original_invariant
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} {L : Cylinder r}
    (hL : IsAugmentedCylinder A L) (d : Cell (r + 1)) (hd : d ∈ L.children) :
    SignInvariant A d.carrier := by
  intro P hP
  rcases hL.2.2.2 P hP with hfam | hzero
  · exact L.invariant d hd P hfam
  · apply SignInvariantPoly.of_eq_zero
    intro z hz
    have hzinit : Fin.init z ∈ L.parent.carrier :=
      LiftShape.init_mem (L.children_shape d hd) hz
    have hp0 := hzero (Fin.init z) hzinit
    calc
      MvPolynomial.eval z P =
          MvPolynomial.eval (Fin.snoc (Fin.init z) (z (Fin.last r))) P := by
        rw [Fin.snoc_init_self]
      _ = Polynomial.eval (z (Fin.last r)) (fiberPoly r P (Fin.init z)) :=
        (fiberPoly_eval r P (Fin.init z) (z (Fin.last r))).symm
      _ = 0 := by rw [hp0, Polynomial.eval_zero]

/-- Construct one augmented invariant cylinder on a base cell. -/
theorem exists_augmented_cylinder
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} (S : Cell r)
    (hproj : SignInvariant (augProj A) S.carrier) :
    ∃ L : Cylinder r, L.parent = S ∧ IsCylinderPartition L ∧
      IsAugmentedCylinder A L ∧ ∀ d ∈ L.children, SignInvariant A d.carrier := by
  classical
  let B := localAugPolySet A S.sample
  have hfiberB : ∀ Q ∈ B, ∀ a ∈ S.carrier, fiberPoly r Q a ≠ 0 := by
    intro Q hQ
    exact fiberPoly_ne_zero_of_mem_localAugPolySet S.sample_mem hproj hQ
  have hprojB : SignInvariant (collinsProj B) S.carrier :=
    signInvariant_collinsProj_localAugPolySet S.sample hproj
  obtain ⟨W⟩ := exists_liftingWitness_of_nonzero_fibers (A := B) S hprojB hfiberB
  have hinvB : ∀ d ∈ liftCells S W.roots, SignInvariant B d.carrier := by
    intro d hd
    exact LiftShape.signInvariant W (liftCells_shape S W.roots d hd)
  have hsection : ∀ i a, a ∈ S.carrier →
      ∃ P ∈ B, Polynomial.eval (W.roots.f i a) (fiberPoly r P a) = 0 := by
    intro i a ha
    rcases W.section_root i a ha with ⟨P, hP, hroot⟩
    exact ⟨P, W.retained_subset hP, hroot⟩
  let L := Cylinder.canonical S W.roots B hinvB hsection
  have hpart : IsCylinderPartition L :=
    IsCylinderPartition.canonical S W.roots B hinvB hsection
  have haug : IsAugmentedCylinder A L := by
    refine ⟨?_, hfiberB, ?_, ?_⟩
    · exact nonzeroFibers_subset (augPolySet A) S.sample
    · intro Q hQ D hD
      exact localAugPolySet_derivative_dichotomy S.sample_mem hproj hQ hD
    · intro P hP
      by_cases hPB : P ∈ B
      · exact Or.inl hPB
      · exact Or.inr (fiberPoly_eq_zero_of_not_mem_nonzeroFibers
          S.sample_mem hproj (subset_augPolySet A hP) hPB)
  refine ⟨L, rfl, hpart, haug, ?_⟩
  intro d hd
  exact IsAugmentedCylinder.original_invariant haug d hd

/-- Recursive provenance recording that every cylinder used the local
    augmented family required by DEFINE. -/
def HasAugmentedProvenance : {r : ℕ} → CAD r →
    Finset (MvPolynomial (Fin r) ℝ) → Prop
  | 0, .zero _, _ => True
  | _ + 1, .succ previous next edges, A =>
      HasAugmentedProvenance previous (augProj A) ∧
        IsParentChildMap previous.decomposition next edges ∧
        (∀ L ∈ edges, IsAugmentedCylinder A L)

/-- Augmented provenance descends to the preceding CAD level. -/
theorem HasAugmentedProvenance.previous {T : CAD (r + 1)}
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    (hT : HasAugmentedProvenance T A) :
    HasAugmentedProvenance T.previous (augProj A) := by
  cases T with
  | succ previous next edges => exact hT.1

/-- There is an invariant CAD with full augmented provenance. -/
theorem exists_augmented_cad (r : ℕ) (A : Finset (MvPolynomial (Fin r) ℝ)) :
    ∃ T : CAD r, IsCAD T ∧ CADInvariant A T.cells ∧ HasAugmentedProvenance T A := by
  classical
  induction r with
  | zero => exact ⟨baseCAD, trivial, baseCAD_invariant A, trivial⟩
  | succ r ih =>
    rcases ih (augProj A) with ⟨Tprev, hprev, hinv, hprov⟩
    have hcyl : ∀ c : {c : Cell r // c ∈ Tprev.cells},
        ∃ L : Cylinder r, L.parent = c.1 ∧ IsCylinderPartition L ∧
          IsAugmentedCylinder A L ∧ ∀ d ∈ L.children, SignInvariant A d.carrier := by
      intro c
      exact exists_augmented_cylinder (A := A) c.1 (hinv c.1 c.2)
    choose L hparent hpart haug hinvL using hcyl
    let edges : List (Cylinder r) := Tprev.cells.attach.map L
    have hLinj : Function.Injective L := by
      intro c d heq
      apply Subtype.ext
      have hp := congrArg Cylinder.parent heq
      simpa [hparent c, hparent d] using hp
    have hedges_nodup : edges.Nodup :=
      (List.nodup_attach.mpr Tprev.decomposition.cells_nodup).map hLinj
    have hparent_mem : ∀ M ∈ edges, M.parent ∈ Tprev.cells := by
      intro M hM
      rcases List.mem_map.mp hM with ⟨c, hc, rfl⟩
      rw [hparent c]
      exact c.2
    have hcomplete : ∀ c ∈ Tprev.cells, ∃ M ∈ edges, M.parent = c := by
      intro c hc
      let cs : {c : Cell r // c ∈ Tprev.cells} := ⟨c, hc⟩
      refine ⟨L cs, ?_, hparent cs⟩
      exact List.mem_map.mpr ⟨cs, List.mem_attach _ _, rfl⟩
    have hunique : ∀ M ∈ edges, ∀ N ∈ edges, M.parent = N.parent → M = N := by
      intro M hM N hN hparentEq
      rcases List.mem_map.mp hM with ⟨c, hc, rfl⟩
      rcases List.mem_map.mp hN with ⟨d, hd, rfl⟩
      apply congrArg L
      apply Subtype.ext
      simpa [hparent c, hparent d] using hparentEq
    have hpart_edges : ∀ M ∈ edges, IsCylinderPartition M := by
      intro M hM
      rcases List.mem_map.mp hM with ⟨c, hc, rfl⟩
      exact hpart c
    have haug_edges : ∀ M ∈ edges, IsAugmentedCylinder A M := by
      intro M hM
      rcases List.mem_map.mp hM with ⟨c, hc, rfl⟩
      exact haug c
    rcases exists_decomposition_lift Tprev.decomposition edges hedges_nodup
      hparent_mem hcomplete hunique hpart_edges with ⟨E, hmap⟩
    let T : CAD (r + 1) := .succ Tprev E edges
    refine ⟨T, ⟨hprev, hmap⟩, ?_, ⟨hprov, hmap, haug_edges⟩⟩
    intro d hd
    have hcells : E.cells = edges.flatMap (fun M => M.children) :=
      hmap.2.2.2.2.1
    have hd' : d ∈ edges.flatMap (fun M => M.children) := by
      rw [← hcells]
      exact hd
    rcases List.mem_flatMap.mp hd' with ⟨M, hM, hdM⟩
    rcases List.mem_map.mp hM with ⟨c, hc, rfl⟩
    exact hinvL c d hdM

end CollinsCAD
