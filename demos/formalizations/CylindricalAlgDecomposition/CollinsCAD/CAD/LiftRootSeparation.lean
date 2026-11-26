import Mathlib
import CAD.CylinderPartition
import Analysis.ThomFamily

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- The finite family of univariate fibres over a base point. -/
noncomputable def fiberFamily (B : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (a : Fin r → ℝ) : Finset (Polynomial ℝ) :=
  B.image (fun P => fiberPoly r P a)

@[simp] theorem mem_fiberFamily {B : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {a : Fin r → ℝ} {q : Polynomial ℝ} :
    q ∈ fiberFamily B a ↔ ∃ P ∈ B, fiberPoly r P a = q := by
  simp [fiberFamily, Finset.mem_image]

/-- A section root is a root of a polynomial in the fibre family. -/
theorem Cylinder.section_root_mem (L : Cylinder r) (i : Fin L.roots.k)
    (a : Fin r → ℝ) (ha : a ∈ L.parent.carrier) :
    ∃ q ∈ fiberFamily L.family a, q.eval (L.roots.f i a) = 0 := by
  rcases L.section_root i a ha with ⟨P, hP, hroot⟩
  exact ⟨fiberPoly r P a, mem_fiberFamily.mpr ⟨P, hP, rfl⟩, hroot⟩

/-- Distinct lifted children over the same base point are separated by a root
    of the cylinder family. -/
theorem LiftShape.rootSeparated_of_ne (L : Cylinder r) {c d : Cell (r + 1)}
    (hc : LiftShape L.parent L.roots c) (hd : LiftShape L.parent L.roots d)
    (hne : c ≠ d) {a : Fin r → ℝ} (ha : a ∈ L.parent.carrier)
    {x y : ℝ} (hx : Fin.snoc a x ∈ c.carrier) (hy : Fin.snoc a y ∈ d.carrier) :
    RootSeparatedByFamily (fiberFamily L.family a) x y := by
  have hroot (i : Fin L.roots.k) : ∃ q ∈ fiberFamily L.family a,
      q.eval (L.roots.f i a) = 0 := Cylinder.section_root_mem L i a ha
  cases hc with
  | whole hk =>
    cases hd with
    | whole hk' => exact (hne rfl).elim
    | lower i hi => exact Fin.elim0 (by simpa [hk] using i)
    | graph i => exact Fin.elim0 (by simpa [hk] using i)
    | bounded i j hj => exact Fin.elim0 (by simpa [hk] using i)
    | upper i hi => exact Fin.elim0 (by simpa [hk] using i)
  | lower i hi =>
    have hxi := Cell.mem_lower.mp hx
    simp only [Fin.init_snoc, Fin.snoc_last] at hxi
    cases hd with
    | whole hk => exact Fin.elim0 (by simpa [hk] using i)
    | lower j hj =>
      have hij : i = j := by
        apply Fin.ext
        omega
      subst j
      exact (hne rfl).elim
    | graph j =>
      have hyj := Cell.mem_graph.mp hy
      simp only [Fin.init_snoc, Fin.snoc_last] at hyj
      have hij : i ≤ j := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [hi]
        omega
      have hord : L.roots.f i a ≤ L.roots.f j a := by
        by_cases hEq : i = j
        · subst j
          exact le_rfl
        · exact (L.roots.ordered i j a ha (lt_of_le_of_ne hij hEq)).le
      rcases hroot j with ⟨q, hq, hqroot⟩
      exact ⟨L.roots.f j a, Or.inl ⟨hxi.2.le.trans hord, hyj.2.ge⟩,
        q, hq, hqroot⟩
    | bounded j l hjl =>
      have hyl := Cell.mem_bounded.mp hy
      simp only [Fin.init_snoc, Fin.snoc_last] at hyl
      have hij : i ≤ j := by
        apply Fin.le_iff_val_le_val.mpr
        rw [hi]
        exact Nat.zero_le _
      rcases hroot i with ⟨q, hq, hqroot⟩
      refine ⟨L.roots.f i a, ?_, q, hq, hqroot⟩
      by_cases hEq : i = j
      · subst j
        exact Or.inl ⟨hxi.2.le, hyl.2.1.le⟩
      · have hij' : i < j := lt_of_le_of_ne hij hEq
        have hord := L.roots.ordered i j a ha hij'
        exact Or.inl ⟨hxi.2.le, hord.le.trans hyl.2.1.le⟩
    | upper j hj =>
      have hyj := Cell.mem_upper.mp hy
      simp only [Fin.init_snoc, Fin.snoc_last] at hyj
      have hij : i ≤ j := by
        apply Fin.le_iff_val_le_val.mpr
        rw [hi]
        exact Nat.zero_le _
      rcases hroot j with ⟨q, hq, hqroot⟩
      refine ⟨L.roots.f j a, ?_, q, hq, hqroot⟩
      by_cases hEq : i = j
      · subst i
        exact Or.inl ⟨hxi.2.le, hyj.2.le⟩
      · have hij' : i < j := lt_of_le_of_ne hij hEq
        have hord := L.roots.ordered i j a ha hij'
        exact Or.inl ⟨hxi.2.le.trans hord.le, hyj.2.le⟩
  | graph i =>
    have hxi := Cell.mem_graph.mp hx
    simp only [Fin.init_snoc, Fin.snoc_last] at hxi
    rcases hroot i with ⟨q, hq, hqroot⟩
    refine ⟨L.roots.f i a, ?_, q, hq, hqroot⟩
    cases hd with
    | whole hk => exact Fin.elim0 (by simpa [hk] using i)
    | lower j hj =>
      rcases le_total x y with hxy | hyx
      · exact Or.inl ⟨hxi.2.le, by simpa [hxi.2] using hxy⟩
      · exact Or.inr ⟨by simpa [hxi.2] using hyx, hxi.2.symm.le⟩
    | graph j =>
      rcases le_total x y with hxy | hyx
      · exact Or.inl ⟨hxi.2.le, by simpa [hxi.2] using hxy⟩
      · exact Or.inr ⟨by simpa [hxi.2] using hyx, hxi.2.symm.le⟩
    | bounded j l hjl =>
      rcases le_total x y with hxy | hyx
      · exact Or.inl ⟨hxi.2.le, by simpa [hxi.2] using hxy⟩
      · exact Or.inr ⟨by simpa [hxi.2] using hyx, hxi.2.symm.le⟩
    | upper j hj =>
      rcases le_total x y with hxy | hyx
      · exact Or.inl ⟨hxi.2.le, by simpa [hxi.2] using hxy⟩
      · exact Or.inr ⟨by simpa [hxi.2] using hyx, hxi.2.symm.le⟩
  | bounded i j hj =>
    have hxi := Cell.mem_bounded.mp hx
    simp only [Fin.init_snoc, Fin.snoc_last] at hxi
    cases hd with
    | whole hk => exact Fin.elim0 (by simpa [hk] using i)
    | lower l hl =>
      have hyl := Cell.mem_lower.mp hy
      simp only [Fin.init_snoc, Fin.snoc_last] at hyl
      have hli : l ≤ i := by
        apply Fin.le_iff_val_le_val.mpr
        rw [hl]
        exact Nat.zero_le _
      rcases hroot l with ⟨q, hq, hqroot⟩
      refine ⟨L.roots.f l a, ?_, q, hq, hqroot⟩
      by_cases hEq : l = i
      · subst l
        exact Or.inr ⟨hyl.2.le, hxi.2.1.le⟩
      · have hli' : l < i := lt_of_le_of_ne hli hEq
        have hord := L.roots.ordered l i a ha hli'
        exact Or.inr ⟨hyl.2.le, hord.le.trans hxi.2.1.le⟩
    | graph l =>
      rcases hroot l with ⟨q, hq, hqroot⟩
      refine ⟨L.roots.f l a, ?_, q, hq, hqroot⟩
      have hyl := Cell.mem_graph.mp hy
      simp only [Fin.init_snoc, Fin.snoc_last] at hyl
      by_cases hil : l < i
      · have hord := L.roots.ordered l i a ha hil
        exact Or.inr ⟨hyl.2.le, hord.le.trans hxi.2.1.le⟩
      · by_cases hli : i < l
        · have hjl : j ≤ l := by
            apply Fin.le_iff_val_le_val.mpr
            omega
          by_cases hEq : j = l
          · subst l
            exact Or.inl ⟨hxi.2.2.le, hyl.2.ge⟩
          · have hjl' : j < l := lt_of_le_of_ne hjl hEq
            have hord := L.roots.ordered j l a ha hjl'
            exact Or.inl ⟨(hxi.2.2.trans hord).le, hyl.2.ge⟩
        · have hEq : l = i := le_antisymm (le_of_not_gt hli) (le_of_not_gt hil)
          subst l
          exact Or.inr ⟨hyl.2.le, hxi.2.1.le⟩
    | bounded k l hkl =>
      have hyl := Cell.mem_bounded.mp hy
      simp only [Fin.init_snoc, Fin.snoc_last] at hyl
      have hik : i ≠ k := by
        intro heq
        subst k
        have hjl : j = l := Fin.ext (by omega)
        subst l
        exact hne rfl
      have hsplit : j.val ≤ k.val ∨ l.val ≤ i.val := by omega
      rcases hsplit with hjk | hli
      · rcases hroot j with ⟨q, hq, hqroot⟩
        refine ⟨L.roots.f j a, ?_, q, hq, hqroot⟩
        by_cases hEq : j = k
        · subst k
          exact Or.inl ⟨hxi.2.2.le, hyl.2.1.le⟩
        · have hjk' : j < k := lt_of_le_of_ne hjk hEq
          have hord := L.roots.ordered j k a ha hjk'
          exact Or.inl ⟨hxi.2.2.le, hord.le.trans hyl.2.1.le⟩
      · rcases hroot l with ⟨q, hq, hqroot⟩
        refine ⟨L.roots.f l a, ?_, q, hq, hqroot⟩
        by_cases hEq : l = i
        · subst l
          exact Or.inr ⟨hyl.2.2.le, hxi.2.1.le⟩
        · have hli' : l < i := lt_of_le_of_ne hli hEq
          have hord := L.roots.ordered l i a ha hli'
          exact Or.inr ⟨hyl.2.2.le, hord.le.trans hxi.2.1.le⟩
    | upper k hk =>
      have hyk := Cell.mem_upper.mp hy
      simp only [Fin.init_snoc, Fin.snoc_last] at hyk
      have hjk : j ≤ k := by
        apply Fin.le_iff_val_le_val.mpr
        have hklast := hk
        have hjval := hj
        omega
      rcases hroot j with ⟨q, hq, hqroot⟩
      refine ⟨L.roots.f j a, ?_, q, hq, hqroot⟩
      by_cases hEq : j = k
      · subst k
        exact Or.inl ⟨hxi.2.2.le, hyk.2.le⟩
      · have hjk' : j < k := lt_of_le_of_ne hjk hEq
        have hord := L.roots.ordered j k a ha hjk'
        exact Or.inl ⟨hxi.2.2.le, hord.le.trans hyk.2.le⟩
  | upper i hi =>
    have hxi := Cell.mem_upper.mp hx
    simp only [Fin.init_snoc, Fin.snoc_last] at hxi
    cases hd with
    | whole hk => exact Fin.elim0 (by simpa [hk] using i)
    | lower j hj =>
      have hyj := Cell.mem_lower.mp hy
      simp only [Fin.init_snoc, Fin.snoc_last] at hyj
      have hji : j ≤ i := by
        apply Fin.le_iff_val_le_val.mpr
        omega
      rcases hroot j with ⟨q, hq, hqroot⟩
      refine ⟨L.roots.f j a, ?_, q, hq, hqroot⟩
      by_cases hEq : j = i
      · subst i
        exact Or.inr ⟨hyj.2.le, hxi.2.le⟩
      · have hji' : j < i := lt_of_le_of_ne hji hEq
        have hord := L.roots.ordered j i a ha hji'
        exact Or.inr ⟨hyj.2.le, hord.le.trans hxi.2.le⟩
    | graph j =>
      have hyj := Cell.mem_graph.mp hy
      simp only [Fin.init_snoc, Fin.snoc_last] at hyj
      have hji : j ≤ i := by
        apply Fin.le_iff_val_le_val.mpr
        omega
      rcases hroot i with ⟨q, hq, hqroot⟩
      refine ⟨L.roots.f i a, ?_, q, hq, hqroot⟩
      by_cases hEq : j = i
      · subst j
        exact Or.inr ⟨hyj.2.le, hxi.2.le⟩
      · have hji' : j < i := lt_of_le_of_ne hji hEq
        have hord := L.roots.ordered j i a ha hji'
        exact Or.inr ⟨hyj.2.le.trans hord.le, hxi.2.le⟩
    | bounded j l hjl =>
      have hyj := Cell.mem_bounded.mp hy
      simp only [Fin.init_snoc, Fin.snoc_last] at hyj
      have hli : l ≤ i := by
        apply Fin.le_iff_val_le_val.mpr
        omega
      rcases hroot i with ⟨q, hq, hqroot⟩
      refine ⟨L.roots.f i a, ?_, q, hq, hqroot⟩
      by_cases hEq : l = i
      · subst l
        exact Or.inr ⟨hyj.2.2.le, hxi.2.le⟩
      · have hli' : l < i := lt_of_le_of_ne hli hEq
        have hord := L.roots.ordered l i a ha hli'
        exact Or.inr ⟨hyj.2.2.le.trans hord.le, hxi.2.le⟩
    | upper j hj =>
      have hij : i = j := by
        apply Fin.ext
        omega
      subst j
      exact (hne rfl).elim

end CollinsCAD
