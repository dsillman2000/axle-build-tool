import Mathlib
import CAD.Cylinder

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- Shapes occurring after the first cell of a lifted child list. -/
inductive TailLiftShape (S : Cell r) (R : RootFamily S.carrier) : Cell (r + 1) → Prop where
  | graph (i : Fin R.k) :
      TailLiftShape S R (Cell.graph S (R.f i) (R.continuous i))
  | bounded (i j : Fin R.k) (hj : j.val = i.val + 1) :
      TailLiftShape S R (Cell.bounded S (R.f i) (R.f j)
        (R.continuous i) (R.continuous j)
        (fun a ha => R.ordered i j a ha (by change i.val < j.val; omega)))
  | upper (i : Fin R.k) (hi : i.val + 1 = R.k) :
      TailLiftShape S R (Cell.upper S (R.f i) (R.continuous i))

/-- Tail shapes are lifted-cell shapes. -/
theorem TailLiftShape.toLiftShape {S : Cell r} {R : RootFamily S.carrier}
    {c : Cell (r + 1)} (h : TailLiftShape S R c) : LiftShape S R c := by
  cases h with
  | graph i => exact .graph i
  | bounded i j hj => exact .bounded i j hj
  | upper i hi => exact .upper i hi

/-- Shift a tail shape one root to the right. -/
theorem TailLiftShape.shift_succ (S : Cell r) (k : ℕ)
    (f : Fin (k + 1) → (Fin r → ℝ) → ℝ)
    (hc : ∀ i, ContinuousOn (f i) S.carrier)
    (ho : ∀ (i j : Fin (k + 1)) (a : Fin r → ℝ),
      a ∈ S.carrier → i < j → f i a < f j a)
    (c : Cell (r + 1)) (h : TailLiftShape S
      ⟨k, (fun i => f i.succ), (fun i => hc i.succ),
        (fun i j a ha hij => ho i.succ j.succ a ha
          (by change i.val + 1 < j.val + 1; omega))⟩ c) :
    TailLiftShape S ⟨k + 1, f, hc, ho⟩ c := by
  cases h with
  | graph i => exact TailLiftShape.graph (R := ⟨k + 1, f, hc, ho⟩) i.succ
  | bounded i j hj =>
      exact TailLiftShape.bounded (R := ⟨k + 1, f, hc, ho⟩)
        i.succ j.succ (by simpa using hj)
  | upper i hi =>
      exact TailLiftShape.upper (R := ⟨k + 1, f, hc, ho⟩)
        i.succ (by simpa using hi)

/-- Every cell after the first has a tail shape. -/
theorem liftCellsAux_tail_shape (S : Cell r) (k : ℕ)
    (f : Fin k → (Fin r → ℝ) → ℝ)
    (hc : ∀ i, ContinuousOn (f i) S.carrier)
    (ho : ∀ (i j : Fin k) (a : Fin r → ℝ),
      a ∈ S.carrier → i < j → f i a < f j a) :
    ∀ c ∈ (liftCellsAux S k f hc ho).tail,
      TailLiftShape S ⟨k, f, hc, ho⟩ c := by
  induction k with
  | zero => simp [liftCellsAux]
  | succ k ih =>
    intro c hmem
    let f' : Fin k → (Fin r → ℝ) → ℝ := fun i => f i.succ
    have hc' : ∀ i, ContinuousOn (f' i) S.carrier := fun i => hc i.succ
    have ho' : ∀ (i j : Fin k) (a : Fin r → ℝ),
        a ∈ S.carrier → i < j → f' i a < f' j a := by
      intro i j a ha hij
      exact ho i.succ j.succ a ha (by change i.val + 1 < j.val + 1; omega)
    have htail := ih f' hc' ho'
    dsimp only [liftCellsAux] at hmem
    split_ifs at hmem with hk
    · change c ∈
        (Cell.graph S (f 0) (hc 0) ::
          Cell.bounded S (f 0) (f ⟨1, by omega⟩) (hc 0) (hc ⟨1, by omega⟩)
            (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by change 0 < 1; omega)) ::
              (liftCellsAux S k f' hc' ho').tail) at hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | rfl | hprev
      · exact .graph 0
      · exact .bounded 0 ⟨1, by change 1 < k + 1; omega⟩ (by simp)
      · exact TailLiftShape.shift_succ S k f hc ho c (htail c hprev)
    · change c ∈
        (Cell.graph S (f 0) (hc 0) ::
          Cell.upper S (f 0) (hc 0) :: (liftCellsAux S k f' hc' ho').tail) at hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | rfl | hprev
      · exact .graph 0
      · exact .upper 0 (by change (0 : ℕ) + 1 = k + 1; omega)
      · exact TailLiftShape.shift_succ S k f hc ho c (htail c hprev)

/-- Every canonical child has one of the lifted-cell shapes. -/
theorem liftCellsAux_shape (S : Cell r) (k : ℕ)
    (f : Fin k → (Fin r → ℝ) → ℝ)
    (hc : ∀ i, ContinuousOn (f i) S.carrier)
    (ho : ∀ (i j : Fin k) (a : Fin r → ℝ),
      a ∈ S.carrier → i < j → f i a < f j a) :
    ∀ c ∈ liftCellsAux S k f hc ho, LiftShape S ⟨k, f, hc, ho⟩ c := by
  induction k with
  | zero =>
    intro c hmem
    have hceq : c = Cell.whole S := by simpa [liftCellsAux] using hmem
    subst c
    exact .whole rfl
  | succ k ih =>
    intro c hmem
    let f' : Fin k → (Fin r → ℝ) → ℝ := fun i => f i.succ
    have hc' : ∀ i, ContinuousOn (f' i) S.carrier := fun i => hc i.succ
    have ho' : ∀ (i j : Fin k) (a : Fin r → ℝ),
        a ∈ S.carrier → i < j → f' i a < f' j a := by
      intro i j a ha hij
      exact ho i.succ j.succ a ha (by change i.val + 1 < j.val + 1; omega)
    have htail := liftCellsAux_tail_shape S k f' hc' ho'
    dsimp only [liftCellsAux] at hmem
    split_ifs at hmem with hk
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        or_assoc] at hmem
      rcases hmem with rfl | rfl | rfl | hprev
      · exact .lower 0 (by simp)
      · exact .graph 0
      · exact .bounded 0 ⟨1, by change 1 < k + 1; omega⟩ (by simp)
      · have hp := htail c hprev
        exact TailLiftShape.toLiftShape (TailLiftShape.shift_succ S k f hc ho c hp)
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        or_assoc] at hmem
      rcases hmem with rfl | rfl | rfl | hprev
      · exact .lower 0 (by simp)
      · exact .graph 0
      · exact .upper 0 (by change (0 : ℕ) + 1 = k + 1; omega)
      · have hp := htail c hprev
        exact TailLiftShape.toLiftShape (TailLiftShape.shift_succ S k f hc ho c hp)

/-- Canonical child lists are nonempty. -/
theorem liftCellsAux_nonempty (S : Cell r) (k : ℕ)
    (f : Fin k → (Fin r → ℝ) → ℝ)
    (hc : ∀ i, ContinuousOn (f i) S.carrier)
    (ho : ∀ (i j : Fin k) (a : Fin r → ℝ),
      a ∈ S.carrier → i < j → f i a < f j a) :
    (liftCellsAux S k f hc ho) ≠ [] := by
  induction k with
  | zero => simp [liftCellsAux]
  | succ k ih =>
    dsimp only [liftCellsAux]
    split_ifs <;> simp

/-- Canonical child lists have exactly `2k+1` cells. -/
theorem liftCellsAux_length (S : Cell r) (k : ℕ)
    (f : Fin k → (Fin r → ℝ) → ℝ)
    (hc : ∀ i, ContinuousOn (f i) S.carrier)
    (ho : ∀ (i j : Fin k) (a : Fin r → ℝ),
      a ∈ S.carrier → i < j → f i a < f j a) :
    (liftCellsAux S k f hc ho).length = 2 * k + 1 := by
  induction k with
  | zero => simp [liftCellsAux]
  | succ k ih =>
    let f' : Fin k → (Fin r → ℝ) → ℝ := fun i => f i.succ
    have hc' : ∀ i, ContinuousOn (f' i) S.carrier := fun i => hc i.succ
    have ho' : ∀ (i j : Fin k) (a : Fin r → ℝ),
        a ∈ S.carrier → i < j → f' i a < f' j a := by
      intro i j a ha hij
      exact ho i.succ j.succ a ha (by change i.val + 1 < j.val + 1; omega)
    have hlen := ih f' hc' ho'
    have hne := liftCellsAux_nonempty S k f' hc' ho'
    have htail : (liftCellsAux S k f' hc' ho').tail.length = 2 * k := by
      cases hlist : liftCellsAux S k f' hc' ho' with
      | nil => simp [hlist] at hne
      | cons a l =>
        rw [hlist] at hlen
        simpa using hlen
    let newCells : List (Cell (r + 1)) :=
      if hk : 0 < k then
        let right : (Fin r → ℝ) → ℝ := f ⟨1, by omega⟩
        [Cell.lower S (f 0) (hc 0),
          Cell.graph S (f 0) (hc 0),
          Cell.bounded S (f 0) right (hc 0) (hc ⟨1, by omega⟩)
            (fun a ha => ho 0 ⟨1, by omega⟩ a ha (by change 0 < 1; omega))]
      else
        [Cell.lower S (f 0) (hc 0), Cell.graph S (f 0) (hc 0),
          Cell.upper S (f 0) (hc 0)]
    change (newCells ++ (liftCellsAux S k f' hc' ho').tail).length = _
    dsimp only [newCells]
    split_ifs <;> simp [htail] <;> omega

end CollinsCAD
