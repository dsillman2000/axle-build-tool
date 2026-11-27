import Mathlib
import CAD.CylinderGeometry

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- The first canonical child is the whole cylinder when there are no roots,
    and otherwise the sector below the first root. -/
theorem liftCellsAux_head (S : Cell r) (k : ℕ)
    (f : Fin k → (Fin r → ℝ) → ℝ)
    (hc : ∀ i, ContinuousOn (f i) S.carrier)
    (ho : ∀ (i j : Fin k) (a : Fin r → ℝ),
      a ∈ S.carrier → i < j → f i a < f j a) :
    ∃ h rest, liftCellsAux S k f hc ho = h :: rest ∧
      ((k = 0 ∧ h = Cell.whole S) ∨
        (∃ i : Fin k, i.val = 0 ∧ h = Cell.lower S (f i) (hc i))) := by
  cases k with
  | zero => exact ⟨Cell.whole S, [], rfl, Or.inl ⟨rfl, rfl⟩⟩
  | succ k =>
    dsimp only [liftCellsAux]
    split_ifs with hk
    · refine ⟨Cell.lower S (f 0) (hc 0),
        (Cell.graph S (f 0) (hc 0) ::
          Cell.bounded S (f 0) (f ⟨1, by omega⟩) (hc 0) (hc ⟨1, by omega⟩)
            (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by change 0 < 1; omega)) :: []) ++
          (liftCellsAux S k (fun i => f i.succ) (fun i => hc i.succ)
            (fun i j a ha hij => ho i.succ j.succ a ha
              (by change i.val + 1 < j.val + 1; omega))).tail, rfl,
        Or.inr ⟨0, by simp, rfl⟩⟩
    · refine ⟨Cell.lower S (f 0) (hc 0),
        (Cell.graph S (f 0) (hc 0) :: Cell.upper S (f 0) (hc 0) :: []) ++
          (liftCellsAux S k (fun i => f i.succ) (fun i => hc i.succ)
            (fun i j a ha hij => ho i.succ j.succ a ha
              (by change i.val + 1 < j.val + 1; omega))).tail, rfl,
        Or.inr ⟨0, by simp, rfl⟩⟩

/-- Every point over a base cell lies in a canonical lifted child. -/
theorem liftCellsAux_cover (S : Cell r) (k : ℕ)
    (f : Fin k → (Fin r → ℝ) → ℝ)
    (hc : ∀ i, ContinuousOn (f i) S.carrier)
    (ho : ∀ (i j : Fin k) (a : Fin r → ℝ),
      a ∈ S.carrier → i < j → f i a < f j a) :
    ∀ a ∈ S.carrier, ∀ x : ℝ,
      ∃ c ∈ liftCellsAux S k f hc ho, Fin.snoc a x ∈ c.carrier := by
  induction k with
  | zero =>
    intro a ha x
    refine ⟨Cell.whole S, by simp [liftCellsAux], ?_⟩
    simp [Cell.mem_whole, ha]
  | succ k ih =>
    let f' : Fin k → (Fin r → ℝ) → ℝ := fun i => f i.succ
    have hc' : ∀ i, ContinuousOn (f' i) S.carrier := fun i => hc i.succ
    have ho' : ∀ (i j : Fin k) (a : Fin r → ℝ),
        a ∈ S.carrier → i < j → f' i a < f' j a := by
      intro i j a ha hij
      exact ho i.succ j.succ a ha (by change i.val + 1 < j.val + 1; omega)
    have htailcover := ih f' hc' ho'
    intro a ha x
    by_cases hleft : x < f 0 a
    · refine ⟨Cell.lower S (f 0) (hc 0), ?_, ?_⟩
      · change Cell.lower S (f 0) (hc 0) ∈
          (if h : 0 < k then
            [Cell.lower S (f 0) (hc 0),
              Cell.graph S (f 0) (hc 0),
              Cell.bounded S (f 0) (f ⟨1, by omega⟩) (hc 0) (hc ⟨1, by omega⟩)
                (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by change 0 < 1; omega))]
          else
            [Cell.lower S (f 0) (hc 0), Cell.graph S (f 0) (hc 0),
              Cell.upper S (f 0) (hc 0)]) ++
            (liftCellsAux S k f' hc' ho').tail
        split_ifs <;> simp
      · simp [Cell.mem_lower, ha, hleft]
    · by_cases heq : x = f 0 a
      · refine ⟨Cell.graph S (f 0) (hc 0), ?_, ?_⟩
        · change Cell.graph S (f 0) (hc 0) ∈
            (if h : 0 < k then
              [Cell.lower S (f 0) (hc 0),
                Cell.graph S (f 0) (hc 0),
                Cell.bounded S (f 0) (f ⟨1, by omega⟩) (hc 0) (hc ⟨1, by omega⟩)
                  (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by change 0 < 1; omega))]
            else
              [Cell.lower S (f 0) (hc 0), Cell.graph S (f 0) (hc 0),
                Cell.upper S (f 0) (hc 0)]) ++
              (liftCellsAux S k f' hc' ho').tail
          split_ifs <;> simp
        · simp [Cell.mem_graph, ha, heq]
      · have hgt : f 0 a < x := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm heq)
        by_cases hk : 0 < k
        · let right : (Fin r → ℝ) → ℝ := f ⟨1, by omega⟩
          have hlr : f 0 a < right a :=
            ho 0 ⟨1, by omega⟩ a ha (by change 0 < 1; omega)
          by_cases hxr : x < right a
          · refine ⟨Cell.bounded S (f 0) right (hc 0) (hc ⟨1, by omega⟩)
              (fun b hb => ho 0 ⟨1, by omega⟩ b hb (by change 0 < 1; omega)), ?_, ?_⟩
            · change Cell.bounded S (f 0) right (hc 0) (hc ⟨1, by omega⟩)
                (fun b hb => ho 0 ⟨1, by omega⟩ b hb (by change 0 < 1; omega)) ∈
                (if h : 0 < k then
                  [Cell.lower S (f 0) (hc 0),
                    Cell.graph S (f 0) (hc 0),
                    Cell.bounded S (f 0) (f ⟨1, by omega⟩) (hc 0) (hc ⟨1, by omega⟩)
                      (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by change 0 < 1; omega))]
                else
                  [Cell.lower S (f 0) (hc 0), Cell.graph S (f 0) (hc 0),
                    Cell.upper S (f 0) (hc 0)]) ++
                  (liftCellsAux S k f' hc' ho').tail
              rw [dite_eq_left hk]
              dsimp [right]
              change Cell.bounded S (f 0) (f ⟨1, by omega⟩) (hc 0) (hc ⟨1, by omega⟩)
                (fun b hb => ho 0 ⟨1, by omega⟩ b hb (by change 0 < 1; omega)) ∈
                [Cell.lower S (f 0) (hc 0),
                  Cell.graph S (f 0) (hc 0),
                  Cell.bounded S (f 0) (f ⟨1, by omega⟩) (hc 0) (hc ⟨1, by omega⟩)
                    (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by change 0 < 1; omega))] ++
                  (liftCellsAux S k f' hc' ho').tail
              simp
            · simp [Cell.mem_bounded, ha, hgt, hxr]
          · have hrx : right a ≤ x := le_of_not_gt hxr
            rcases htailcover a ha x with ⟨c, hcmem, hxc⟩
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
            have hctail : c ∈ rest := by
              rcases List.mem_cons.mp (by simpa [hlist] using hcmem) with hchead | hcrest
              · subst c
                rw [hhead, Cell.mem_lower] at hxc
                simp only [Fin.init_snoc, Fin.snoc_last] at hxc
                exact (not_lt_of_ge hrx hxc.2).elim
              · exact hcrest
            refine ⟨c, ?_, hxc⟩
            have hcur : c ∈
                (Cell.lower S (f 0) (hc 0) ::
                  Cell.graph S (f 0) (hc 0) ::
                    Cell.bounded S (f 0) right (hc 0) (hc ⟨1, by omega⟩)
                      (fun b hb => ho 0 ⟨1, by omega⟩ b hb (by change 0 < 1; omega)) :: []) ++
                      (liftCellsAux S k f' hc' ho').tail := by
              apply List.mem_append_right
              rw [hlist]
              exact hctail
            simpa [liftCellsAux, hk] using hcur
        · refine ⟨Cell.upper S (f 0) (hc 0), ?_, ?_⟩
          · change Cell.upper S (f 0) (hc 0) ∈
              (if h : 0 < k then
                [Cell.lower S (f 0) (hc 0),
                  Cell.graph S (f 0) (hc 0),
                  Cell.bounded S (f 0) (f ⟨1, by omega⟩) (hc 0) (hc ⟨1, by omega⟩)
                    (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by change 0 < 1; omega))]
              else
                [Cell.lower S (f 0) (hc 0), Cell.graph S (f 0) (hc 0),
                  Cell.upper S (f 0) (hc 0)]) ++
                (liftCellsAux S k f' hc' ho').tail
            rw [dite_eq_right hk]
            simp
          · simp [Cell.mem_upper, ha, hgt]

/-- Fibre coverage for the public child list. -/
theorem liftCells_cover (S : Cell r) (R : RootFamily S.carrier) :
    ∀ a ∈ S.carrier, ∀ x : ℝ,
      ∃ c ∈ liftCells S R, Fin.snoc a x ∈ c.carrier := by
  exact liftCellsAux_cover S R.k R.f R.continuous R.ordered

/-- Every lifted shape meets every base fibre. -/
theorem LiftShape.fiber_nonempty {S : Cell r} {R : RootFamily S.carrier}
    {c : Cell (r + 1)} (h : LiftShape S R c) :
    ∀ a ∈ S.carrier, ∃ x : ℝ, Fin.snoc a x ∈ c.carrier := by
  cases h with
  | whole hk =>
    intro a ha
    exact ⟨0, by simp [Cell.mem_whole, ha]⟩
  | lower i hi =>
    intro a ha
    refine ⟨R.f i a - 1, ?_⟩
    simp [Cell.mem_lower, ha]
  | graph i =>
    intro a ha
    exact ⟨R.f i a, by simp [Cell.mem_graph, ha]⟩
  | bounded i j hj =>
    intro a ha
    have hij : i < j := by change i.val < j.val; omega
    have hlt := R.ordered i j a ha hij
    refine ⟨(R.f i a + R.f j a) / 2, ?_⟩
    simp only [Cell.mem_bounded, Fin.init_snoc, Fin.snoc_last]
    exact ⟨ha, by linarith, by linarith⟩
  | upper i hi =>
    intro a ha
    refine ⟨R.f i a + 1, ?_⟩
    simp [Cell.mem_upper, ha]

/-- Canonical child samples are cylindrical. -/
theorem LiftShape.sample_init {S : Cell r} {R : RootFamily S.carrier}
    {c : Cell (r + 1)} (h : LiftShape S R c) :
    Fin.init c.sample = S.sample := by
  cases h <;> simp [Cell.whole, Cell.lower, Cell.graph, Cell.bounded, Cell.upper]

/-- Every canonical child meets every base fibre. -/
theorem liftCells_fiber_nonempty (S : Cell r) (R : RootFamily S.carrier) :
    ∀ a ∈ S.carrier, ∀ c ∈ liftCells S R,
      ∃ x : ℝ, Fin.snoc a x ∈ c.carrier := by
  intro a ha c hc
  exact LiftShape.fiber_nonempty
    (liftCellsAux_shape S R.k R.f R.continuous R.ordered c hc) a ha

/-- Canonical child samples have the parent's base coordinates. -/
theorem liftCells_sample_init (S : Cell r) (R : RootFamily S.carrier) :
    ∀ c ∈ liftCells S R, Fin.init c.sample = S.sample := by
  intro c hc
  exact LiftShape.sample_init
    (liftCellsAux_shape S R.k R.f R.continuous R.ordered c hc)

/-- The public child list has the expected shape and length. -/
theorem liftCells_shape (S : Cell r) (R : RootFamily S.carrier) :
    ∀ c ∈ liftCells S R, LiftShape S R c := by
  exact liftCellsAux_shape S R.k R.f R.continuous R.ordered

theorem liftCells_length (S : Cell r) (R : RootFamily S.carrier) :
    (liftCells S R).length = 2 * R.k + 1 := by
  exact liftCellsAux_length S R.k R.f R.continuous R.ordered

theorem liftCells_nonempty (S : Cell r) (R : RootFamily S.carrier) :
    (liftCells S R) ≠ [] := by
  exact liftCellsAux_nonempty S R.k R.f R.continuous R.ordered

end CollinsCAD
