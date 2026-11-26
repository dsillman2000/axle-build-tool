import Mathlib
import CAD.CylinderCoverage

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- A point in a lifted child projects into the parent cell. -/
theorem LiftShape.init_mem {S : Cell r} {R : RootFamily S.carrier}
    {c : Cell (r + 1)} (h : LiftShape S R c)
    {z : Fin (r + 1) → ℝ} (hz : z ∈ c.carrier) : Fin.init z ∈ S.carrier := by
  cases h with
  | whole hk => exact Cell.mem_whole.mp hz
  | lower i hi => exact (Cell.mem_lower.mp hz).1
  | graph i => exact (Cell.mem_graph.mp hz).1
  | bounded i j hj => exact (Cell.mem_bounded.mp hz).1
  | upper i hi => exact (Cell.mem_upper.mp hz).1

/-- Pairwise relations extend over list append. -/
theorem listPairwiseAppend {α : Type*} {R : α → α → Prop}
    {l₁ l₂ : List α} (h₁ : l₁.Pairwise R) (h₂ : l₂.Pairwise R)
    (hcross : ∀ a ∈ l₁, ∀ b ∈ l₂, R a b) : (l₁ ++ l₂).Pairwise R := by
  induction l₁ with
  | nil => simpa using h₂
  | cons a l ih =>
    have h₁' := List.pairwise_cons.mp h₁
    rw [List.cons_append, List.pairwise_cons]
    constructor
    · intro b hb
      rcases List.mem_append.mp hb with hbl | hb₂
      · exact h₁'.1 b hbl
      · exact hcross a (by simp) b hb₂
    · exact ih h₁'.2 (fun x hx y hy => hcross x (by simp [hx]) y hy)

/-- Canonical lifted children are pairwise disjoint. -/
theorem liftCellsAux_pairwise_disjoint (S : Cell r) (k : ℕ)
    (f : Fin k → (Fin r → ℝ) → ℝ)
    (hc : ∀ i, ContinuousOn (f i) S.carrier)
    (ho : ∀ (i j : Fin k) (a : Fin r → ℝ),
      a ∈ S.carrier → i < j → f i a < f j a) :
    (liftCellsAux S k f hc ho).Pairwise
      (fun c d => Disjoint c.carrier d.carrier) := by
  induction k with
  | zero => simp [liftCellsAux]
  | succ k ih =>
    let f' : Fin k → (Fin r → ℝ) → ℝ := fun i => f i.succ
    have hc' : ∀ i, ContinuousOn (f' i) S.carrier := fun i => hc i.succ
    have ho' : ∀ (i j : Fin k) (a : Fin r → ℝ),
        a ∈ S.carrier → i < j → f' i a < f' j a := by
      intro i j a ha hij
      exact ho i.succ j.succ a ha (by change i.val + 1 < j.val + 1; omega)
    have hprev := ih f' hc' ho'
    have hnew : (if h : 0 < k then
        [Cell.lower S (f 0) (hc 0),
          Cell.graph S (f 0) (hc 0),
          Cell.bounded S (f 0) (f ⟨1, by omega⟩) (hc 0) (hc ⟨1, by omega⟩)
            (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by
              apply Fin.val_fin_lt.mpr
              change (0 : ℕ) < 1
              omega))]
      else
        [Cell.lower S (f 0) (hc 0), Cell.graph S (f 0) (hc 0),
          Cell.upper S (f 0) (hc 0)]).Pairwise
        (fun c d => Disjoint c.carrier d.carrier) := by
      split_ifs with hk
      · have hlr : ∀ a ∈ S.carrier,
            f 0 a < f ⟨1, by omega⟩ a :=
          fun a ha => ho 0 ⟨1, by omega⟩ a ha (by
              apply Fin.val_fin_lt.mpr
              change (0 : ℕ) < 1
              omega)
        rw [List.pairwise_cons]
        constructor
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · rw [Set.disjoint_left]
            intro z hz₁ hz₂
            have h₁ := Cell.mem_lower.mp hz₁
            have h₂ := Cell.mem_graph.mp hz₂
            rw [h₂.2] at h₁
            exact (lt_irrefl _ h₁.2)
          · rcases List.mem_cons.mp hd with rfl | hnil
            · rw [Set.disjoint_left]
              intro z hz₁ hz₂
              have h₁ := Cell.mem_lower.mp hz₁
              have h₂ := Cell.mem_bounded.mp hz₂
              linarith
            · simp at hnil
        · rw [List.pairwise_cons]
          constructor
          · intro d hd
            have hd' : d = Cell.bounded S (f 0) (f ⟨1, by omega⟩)
                (hc 0) (hc ⟨1, by omega⟩)
                (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by
              apply Fin.val_fin_lt.mpr
              change (0 : ℕ) < 1
              omega)) :=
              List.mem_singleton.mp hd
            subst d
            rw [Set.disjoint_left]
            intro z hz₁ hz₂
            have h₁ := Cell.mem_graph.mp hz₁
            have h₂ := Cell.mem_bounded.mp hz₂
            linarith
          · simp
      · rw [List.pairwise_cons]
        constructor
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · rw [Set.disjoint_left]
            intro z hz₁ hz₂
            have h₁ := Cell.mem_lower.mp hz₁
            have h₂ := Cell.mem_graph.mp hz₂
            rw [h₂.2] at h₁
            exact (lt_irrefl _ h₁.2)
          · rcases List.mem_cons.mp hd with rfl | hnil
            · rw [Set.disjoint_left]
              intro z hz₁ hz₂
              have h₁ := Cell.mem_lower.mp hz₁
              have h₂ := Cell.mem_upper.mp hz₂
              linarith
            · simp at hnil
        · rw [List.pairwise_cons]
          constructor
          · intro d hd
            have hd' : d = Cell.upper S (f 0) (hc 0) := List.mem_singleton.mp hd
            subst d
            rw [Set.disjoint_left]
            intro z hz₁ hz₂
            have h₁ := Cell.mem_graph.mp hz₁
            have h₂ := Cell.mem_upper.mp hz₂
            linarith
          · simp
    have htail := hprev.tail
    have hcross : ∀ c ∈ (if h : 0 < k then
        [Cell.lower S (f 0) (hc 0),
          Cell.graph S (f 0) (hc 0),
          Cell.bounded S (f 0) (f ⟨1, by omega⟩) (hc 0) (hc ⟨1, by omega⟩)
            (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by
              apply Fin.val_fin_lt.mpr
              change (0 : ℕ) < 1
              omega))]
      else
        [Cell.lower S (f 0) (hc 0), Cell.graph S (f 0) (hc 0),
          Cell.upper S (f 0) (hc 0)]),
        ∀ d ∈ (liftCellsAux S k f' hc' ho').tail,
          Disjoint c.carrier d.carrier := by
      intro c hcnew d hdtail
      by_cases hk : 0 < k
      · let right : (Fin r → ℝ) → ℝ := f ⟨1, by omega⟩
        have hlr : ∀ a ∈ S.carrier, f 0 a < right a :=
          fun a ha => ho 0 ⟨1, by omega⟩ a ha (by
              apply Fin.val_fin_lt.mpr
              change (0 : ℕ) < 1
              omega)
        obtain ⟨head, rest, hlist, hshape⟩ := liftCellsAux_head S k f' hc' ho'
        have hhead : head = Cell.lower S right (hc ⟨1, by omega⟩) := by
          rcases hshape with hzero | ⟨i, hi, hheadEq⟩
          · omega
          · have hi0 : i = ⟨0, hk⟩ := Fin.ext (by simpa using hi)
            subst i
            have hfzero : f' ⟨0, hk⟩ = right := by
              funext b
              simp [f', right]
            simpa [hfzero] using hheadEq
        have hprev' : (head :: rest).Pairwise
            (fun c d => Disjoint c.carrier d.carrier) := by
          simpa [hlist] using hprev
        have hdhead := (List.pairwise_cons.mp hprev').1 d (by simpa [hlist] using hdtail)
        have hdtailshape := liftCellsAux_tail_shape S k f' hc' ho' d
          (by simpa [hlist] using hdtail)
        have hdinit : ∀ z ∈ d.carrier, Fin.init z ∈ S.carrier :=
          fun z hz => LiftShape.init_mem (TailLiftShape.toLiftShape hdtailshape) hz
        have hright_le : ∀ z ∈ d.carrier, right (Fin.init z) ≤ z (Fin.last r) := by
          intro z hz
          by_contra hnot
          have hlt : z (Fin.last r) < right (Fin.init z) := lt_of_not_ge hnot
          have hzhead : z ∈ head.carrier := by
            rw [hhead]
            exact Cell.mem_lower.mpr ⟨hdinit z hz, hlt⟩
          exact (Set.disjoint_left.mp hdhead) hzhead hz
        rw [dite_eq_left hk] at hcnew
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcnew
        rcases hcnew with rfl | rfl | rfl
        · rw [Set.disjoint_left]
          intro z hz₁ hz₂
          have h₁ := Cell.mem_lower.mp hz₁
          have h₂ := hright_le z hz₂
          have hbase := h₁.1
          have h0r := hlr (Fin.init z) hbase
          dsimp [right] at h₂
          linarith
        · rw [Set.disjoint_left]
          intro z hz₁ hz₂
          have h₁ := Cell.mem_graph.mp hz₁
          have h₂ := hright_le z hz₂
          have h0r := hlr (Fin.init z) h₁.1
          dsimp [right] at h₂
          linarith
        · rw [Set.disjoint_left]
          intro z hz₁ hz₂
          have h₁ := Cell.mem_bounded.mp hz₁
          have h₂ := hright_le z hz₂
          dsimp [right] at h₂
          linarith
      · have hk0 : k = 0 := by omega
        subst k
        simp [liftCellsAux] at hdtail
    change (if h : 0 < k then
        [Cell.lower S (f 0) (hc 0),
          Cell.graph S (f 0) (hc 0),
          Cell.bounded S (f 0) (f ⟨1, by omega⟩) (hc 0) (hc ⟨1, by omega⟩)
            (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by
              apply Fin.val_fin_lt.mpr
              change (0 : ℕ) < 1
              omega))]
      else
        [Cell.lower S (f 0) (hc 0), Cell.graph S (f 0) (hc 0),
          Cell.upper S (f 0) (hc 0)]) ++
        (liftCellsAux S k f' hc' ho').tail |>.Pairwise _
    split_ifs with hk
    · have hnew' := hnew
      have hcross' := hcross
      rw [dite_eq_left hk] at hnew' hcross'
      exact listPairwiseAppend hnew' htail hcross'
    · have hnew' := hnew
      have hcross' := hcross
      rw [dite_eq_right hk] at hnew' hcross'
      exact listPairwiseAppend hnew' htail hcross'

/-- Public canonical children are pairwise disjoint. -/
theorem liftCells_pairwise_disjoint (S : Cell r) (R : RootFamily S.carrier) :
    (liftCells S R).Pairwise (fun c d => Disjoint c.carrier d.carrier) := by
  exact liftCellsAux_pairwise_disjoint S R.k R.f R.continuous R.ordered

/-- Public canonical children contain no duplicates. -/
theorem liftCells_nodup (S : Cell r) (R : RootFamily S.carrier) :
    (liftCells S R).Nodup := by
  have hne : (liftCells S R).Pairwise (fun c d => c ≠ d) := by
    apply (liftCells_pairwise_disjoint S R).imp
    intro c d hdis heq
    subst d
    have hmem : c.sample ∈ c.carrier ∩ c.carrier := ⟨c.sample_mem, c.sample_mem⟩
    exact Set.disjoint_iff.mp hdis hmem
  exact hne.nodup

/-- Construct the canonical cylinder from a root family and its invariance
    proof. -/
noncomputable def Cylinder.canonical (S : Cell r) (R : RootFamily S.carrier)
    (family : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (hinv : ∀ c ∈ liftCells S R, SignInvariant family c.carrier)
    (hsection : ∀ i a, a ∈ S.carrier →
      ∃ P ∈ family, Polynomial.eval (R.f i a) (fiberPoly r P a) = 0) :
    Cylinder r where
  parent := S
  roots := R
  family := family
  children := liftCells S R
  children_length := liftCells_length S R
  children_shape := liftCells_shape S R
  invariant := hinv
  section_root := hsection

/-- The canonical cylinder is a semantic partition. -/
theorem IsCylinderPartition.canonical (S : Cell r) (R : RootFamily S.carrier)
    (family : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (hinv : ∀ c ∈ liftCells S R, SignInvariant family c.carrier)
    (_hsection : ∀ i a, a ∈ S.carrier →
      ∃ P ∈ family, Polynomial.eval (R.f i a) (fiberPoly r P a) = 0) :
    IsCylinderPartition (Cylinder.canonical S R family hinv _hsection) := by
  have hp := liftCells_pairwise_disjoint S R
  refine ⟨liftCells_cover S R, liftCells_fiber_nonempty S R, ?_,
    liftCells_nodup S R, liftCells_sample_init S R⟩
  intro c hc d hd hne
  exact hp.forall hc hd hne

end CollinsCAD
