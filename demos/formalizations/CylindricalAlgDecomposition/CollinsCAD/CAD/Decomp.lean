import Mathlib
import CAD.Structure
import CAD.LiftedSignInvariant

/-!
# Cylindrical decomposition

A CAD level is assembled by lifting every cell of the preceding level with an
invariant cylinder and flattening the resulting child lists. The construction
is uniform from dimension zero: the base decomposition has one empty-tuple
cell, and each successor uses the same parent-to-child map plumbing.
-/

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- Flattened children of distinct certified cylinders are pairwise disjoint. -/
theorem cylinder_flatMap_pairwise (D : Decomposition r)
    (edges : List (Cylinder r)) (hedges_nodup : edges.Nodup)
    (hparent_mem : ∀ L ∈ edges, L.parent ∈ D.cells)
    (hunique : ∀ L ∈ edges, ∀ M ∈ edges, L.parent = M.parent → L = M)
    (hpart : ∀ L ∈ edges, IsCylinderPartition L) :
    (edges.flatMap (fun L => L.children)).Pairwise
      (fun c d => Disjoint c.carrier d.carrier) := by
  induction edges with
  | nil => simp
  | cons L ls ih =>
    have hnod := List.nodup_cons.mp hedges_nodup
    have hLmem : L ∈ (L :: ls) := by simp
    have hLnot : L ∉ ls := hnod.1
    have hparent_ls : ∀ M ∈ ls, M.parent ∈ D.cells :=
      fun M hM => hparent_mem M (by simp [hM])
    have hunique_ls : ∀ M ∈ ls, ∀ N ∈ ls, M.parent = N.parent → M = N :=
      fun M hM N hN => hunique M (by simp [hM]) N (by simp [hN])
    have hpart_ls : ∀ M ∈ ls, IsCylinderPartition M :=
      fun M hM => hpart M (by simp [hM])
    have hrest := ih hnod.2 hparent_ls hunique_ls hpart_ls
    have hLpart := hpart L hLmem
    have hchildren : L.children.Pairwise (fun c d => Disjoint c.carrier d.carrier) :=
      hLpart.2.2.2.1.pairwise_of_forall_ne hLpart.2.2.1
    have hcross : ∀ c ∈ L.children,
        ∀ d ∈ ls.flatMap (fun M => M.children), Disjoint c.carrier d.carrier := by
      intro c hc d hd
      rcases List.mem_flatMap.mp hd with ⟨M, hM, hdM⟩
      have hparent_ne : L.parent ≠ M.parent := by
        intro heq
        have hLM : L = M := hunique L hLmem M (by simp [hM]) heq
        subst M
        exact hLnot hM
      have hdis := D.pairwise_disjoint L.parent (hparent_mem L hLmem)
        M.parent (hparent_mem M (by simp [hM])) hparent_ne
      rw [Set.disjoint_left]
      intro z hzc hzd
      have hzL : Fin.init z ∈ L.parent.carrier :=
        LiftShape.init_mem (L.children_shape c hc) hzc
      have hzM : Fin.init z ∈ M.parent.carrier :=
        LiftShape.init_mem (M.children_shape d hdM) hzd
      exact (Set.disjoint_left.mp hdis) hzL hzM
    exact listPairwiseAppend hchildren hrest hcross

/-- Flatten a complete, unique list of certified cylinders into the next
    semantic decomposition. -/
theorem exists_decomposition_lift (D : Decomposition r)
    (edges : List (Cylinder r))
    (hedges_nodup : edges.Nodup)
    (hparent_mem : ∀ L ∈ edges, L.parent ∈ D.cells)
    (hcomplete : ∀ c ∈ D.cells, ∃ L ∈ edges, L.parent = c)
    (hunique : ∀ L ∈ edges, ∀ M ∈ edges, L.parent = M.parent → L = M)
    (hpart : ∀ L ∈ edges, IsCylinderPartition L) :
    ∃ E : Decomposition (r + 1), IsParentChildMap D E edges := by
  classical
  have hp := cylinder_flatMap_pairwise D edges hedges_nodup hparent_mem hunique hpart
  let E : Decomposition (r + 1) :=
    { cells := edges.flatMap (fun L => L.children)
      cells_nodup := by
        have hne : (edges.flatMap (fun L => L.children)).Pairwise
            (fun c d => c ≠ d) := by
          apply hp.imp
          intro c d hdis heq
          subst d
          have hmem : c.sample ∈ c.carrier ∩ c.carrier :=
            ⟨c.sample_mem, c.sample_mem⟩
          exact Set.disjoint_iff.mp hdis hmem
        exact hne.nodup
      cover := by
        intro x
        let a := Fin.init x
        let t := x (Fin.last r)
        rcases D.cover a with ⟨c, hc, ha⟩
        rcases hcomplete c hc with ⟨L, hL, hparent⟩
        have ha' : a ∈ L.parent.carrier := by simpa [hparent] using ha
        rcases (hpart L hL).1 a ha' t with ⟨d, hd, hxd⟩
        refine ⟨d, ?_, ?_⟩
        · exact List.mem_flatMap.mpr ⟨L, hL, hd⟩
        · simpa [a, t, Fin.snoc_init_self] using hxd
      pairwise_disjoint := by
        intro c hc d hd hne
        exact hp.forall hc hd hne }
  refine ⟨E, ?_⟩
  exact ⟨hedges_nodup, hparent_mem, hcomplete, hunique, rfl, hpart⟩

/-- Assemble a successor CAD from one certified cylinder over every parent
    cell, retaining an arbitrary additional predicate on the cylinders. -/
theorem exists_cad_succ_of_cylinder_builder {r : ℕ}
    (Tprev : CAD r) (hprev : IsCAD Tprev) (P : Cylinder r → Prop)
    (hcyl : ∀ c : {c : Cell r // c ∈ Tprev.cells},
      ∃ L : Cylinder r, L.parent = c.1 ∧ IsCylinderPartition L ∧ P L) :
    ∃ T : CAD (r + 1), IsCAD T ∧ T.previous = Tprev ∧
      ∀ L ∈ T.parentChildren, P L := by
  classical
  choose L hparent hpart hP using hcyl
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
  rcases exists_decomposition_lift Tprev.decomposition edges hedges_nodup
    hparent_mem hcomplete hunique hpart_edges with ⟨E, hmap⟩
  let T : CAD (r + 1) := .succ Tprev E edges
  refine ⟨T, ⟨hprev, hmap⟩, rfl, ?_⟩
  intro M hM
  rcases List.mem_map.mp hM with ⟨c, hc, rfl⟩
  exact hP c

/-- Collins' DECOMP existence theorem, with uniform induction from dimension
    zero. -/
theorem cad_decomp_exists (r : ℕ) (A : Finset (MvPolynomial (Fin r) ℝ)) :
    ∃ T : CAD r, IsCAD T ∧ CADInvariant A T.cells := by
  classical
  induction r with
  | zero => exact ⟨baseCAD, trivial, baseCAD_invariant A⟩
  | succ r ih =>
    rcases ih (collinsProj A) with ⟨Tprev, hprev, hinv⟩
    have hcyl : ∀ c : {c : Cell r // c ∈ Tprev.cells},
        ∃ L : Cylinder r, L.parent = c.1 ∧ IsCylinderPartition L ∧
          ∀ d ∈ L.children, SignInvariant A d.carrier := by
      intro c
      exact exists_cylinder_of_signInvariant_proj c.1 (hinv c.1 c.2)
    rcases exists_cad_succ_of_cylinder_builder Tprev hprev
        (fun L => ∀ d ∈ L.children, SignInvariant A d.carrier) hcyl with
      ⟨T, hT, _hTprev, hinvL⟩
    refine ⟨T, hT, ?_⟩
    intro d hd
    have hmap := IsCAD.parentChildMap hT
    have hd' : d ∈ T.parentChildren.flatMap (fun M => M.children) := by
      rw [← hmap.2.2.2.2.1]
      exact hd
    rcases List.mem_flatMap.mp hd' with ⟨M, hM, hdM⟩
    exact hinvL M hM d hdM

/-- The one-dimensional base case is the uniform DECOMP construction at
    `r = 1`. -/
theorem cad_base_r1 (A : Finset (MvPolynomial (Fin 1) ℝ)) :
    ∃ T : CAD 1, IsCAD T ∧ CADInvariant A T.cells :=
  cad_decomp_exists 1 A

end CollinsCAD
