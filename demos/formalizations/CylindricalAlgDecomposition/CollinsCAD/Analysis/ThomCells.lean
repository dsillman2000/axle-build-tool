import Mathlib

namespace CollinsCAD

open Polynomial

/-- Iterated formal derivative. -/
noncomputable def iteratedDerivative (P : Polynomial ℝ) (k : ℕ) : Polynomial ℝ :=
  Polynomial.derivative^[k] P

@[simp] theorem iteratedDerivative_zero (P : Polynomial ℝ) :
    iteratedDerivative P 0 = P := by
  simp [iteratedDerivative]

@[simp] theorem iteratedDerivative_succ (P : Polynomial ℝ) (k : ℕ) :
    iteratedDerivative P (k + 1) = (iteratedDerivative P k).derivative := by
  simp [iteratedDerivative, Function.iterate_succ_apply']

/-- The full derivative sign vector at a point. -/
noncomputable def derivativeSignVector (P : Polynomial ℝ) (x : ℝ) : ℕ → SignType :=
  fun k => SignType.sign ((iteratedDerivative P k).eval x)

/-- Points having the prescribed signs for all relevant iterated derivatives. -/
def derivativeSignCell (P : Polynomial ℝ) (σ : ℕ → SignType) : Set ℝ :=
  {x | ∀ k ≤ P.natDegree, derivativeSignVector P x k = σ k}

/-- Some prescribed derivative sign is zero. -/
def HasZeroSign (P : Polynomial ℝ) (σ : ℕ → SignType) : Prop :=
  ∃ k ≤ P.natDegree, σ k = 0

/-- A nonempty open interval, including open rays and the whole line. -/
def IsOpenInterval (s : Set ℝ) : Prop :=
  s.Nonempty ∧ IsOpen s ∧ s.OrdConnected

/-- Empty or singleton. -/
def EmptyOrSingleton (s : Set ℝ) : Prop :=
  s = ∅ ∨ ∃ a, s = {a}

/-- Empty or a nonempty open interval. -/
def EmptyOrOpenInterval (s : Set ℝ) : Prop :=
  s = ∅ ∨ IsOpenInterval s

/-- The conclusion of Thom's lemma. -/
def IsThomCell (s : Set ℝ) : Prop :=
  s = ∅ ∨ (∃ a, s = {a}) ∨ IsOpenInterval s

/-- Intersecting an empty-or-singleton set preserves that classification. -/
theorem emptyOrSingleton_inter {s t : Set ℝ}
    (hs : EmptyOrSingleton s) : EmptyOrSingleton (s ∩ t) := by
  rcases hs with rfl | ⟨a, rfl⟩
  · exact Or.inl (by simp)
  · by_cases ha : a ∈ t
    · exact Or.inr ⟨a, by ext x; simp [ha]⟩
    · exact Or.inl (by ext x; simp [ha])

/-- Order-connectedness is preserved by intersection. -/
theorem ordConnected_inter {s t : Set ℝ}
    (hs : s.OrdConnected) (ht : t.OrdConnected) : (s ∩ t).OrdConnected := by
  constructor
  intro x hx y hy z hz
  exact ⟨hs.out' hx.1 hy.1 hz, ht.out' hx.2 hy.2 hz⟩

/-- Intersecting two empty-or-open-interval sets preserves that classification. -/
theorem emptyOrOpenInterval_inter {s t : Set ℝ}
    (hs : EmptyOrOpenInterval s) (ht : EmptyOrOpenInterval t) :
    EmptyOrOpenInterval (s ∩ t) := by
  rcases hs with rfl | hs
  · exact Or.inl (by simp)
  · rcases ht with rfl | ht
    · exact Or.inl (by simp)
    · by_cases hne : (s ∩ t).Nonempty
      · exact Or.inr ⟨hne, hs.2.1.inter ht.2.1, ordConnected_inter hs.2.2 ht.2.2⟩
      · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

/-- Empty-or-open-interval sets are convex, including the empty set. -/
theorem convex_of_emptyOrOpenInterval {s : Set ℝ}
    (hs : EmptyOrOpenInterval s) : Convex ℝ s := by
  rcases hs with rfl | hs
  · exact convex_empty
  · exact convex_iff_ordConnected.mpr hs.2.2

/-- Empty-or-open-interval sets are open, including the empty set. -/
theorem isOpen_of_emptyOrOpenInterval {s : Set ℝ}
    (hs : EmptyOrOpenInterval s) : IsOpen s := by
  rcases hs with rfl | hs
  · exact isOpen_empty
  · exact hs.2.1

/-- The zero set of a strictly monotone or strictly antitone function on a set
    meets that set in at most one point. -/
theorem strictOn_root_emptyOrSingleton {f : ℝ → ℝ} {s : Set ℝ}
    (h : StrictMonoOn f s ∨ StrictAntiOn f s) :
    EmptyOrSingleton (s ∩ {x | f x = 0}) := by
  classical
  by_cases hs : s.Nonempty
  · by_cases hroot : ∃ x ∈ s, f x = 0
    · rcases hroot with ⟨a, ha, hfa⟩
      right
      refine ⟨a, ?_⟩
      ext x
      constructor
      · rintro ⟨hx, hfx⟩
        change f x = 0 at hfx
        rcases h with hmono | hanti
        · rcases lt_trichotomy x a with hxa | hxa | hax
          · have hlt := hmono hx ha hxa
            linarith
          · exact hxa
          · have hlt := hmono ha hx hax
            linarith
        · rcases lt_trichotomy x a with hxa' | hxa' | hax'
          · have hlt := hanti hx ha hxa'
            linarith
          · exact hxa'
          · have hlt := hanti ha hx hax'
            linarith
      · intro hx
        subst x
        exact ⟨ha, hfa⟩
    · left
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hx, hfx⟩
      exact hroot ⟨x, hx, hfx⟩
  · left
    rw [Set.not_nonempty_iff_eq_empty.mp hs]
    simp

/-- A constant nonzero sign level of a strictly increasing function is
    order-connected on an order-connected set. -/
theorem ordConnected_inter_sign_of_strictMono {f : ℝ → ℝ} {s : Set ℝ}
    (hf : StrictMonoOn f s) (hs : s.OrdConnected) (t : SignType) (ht : t ≠ 0) :
    (s ∩ {x | SignType.sign (f x) = t}).OrdConnected := by
  constructor
  intro a ha c hc b hb
  have hbc := Set.mem_Icc.mp hb
  have hbS : b ∈ s := hs.out' ha.1 hc.1 hb
  refine ⟨hbS, ?_⟩
  have hfa := ha.2
  have hfc := hc.2
  have hab' := hf.monotoneOn ha.1 hbS hbc.1
  have hbc' := hf.monotoneOn hbS hc.1 hbc.2
  rcases SignType.trichotomy t with htneg | htzero | htpos
  · rw [htneg] at hfa hfc ⊢
    exact sign_eq_neg_one_iff.mpr (lt_of_le_of_lt hbc' ((sign_eq_neg_one_iff.mp hfc)))
  · exact (ht htzero).elim
  · rw [htpos] at hfa hfc ⊢
    exact sign_eq_one_iff.mpr (lt_of_lt_of_le ((sign_eq_one_iff.mp hfa)) hab')

/-- A constant nonzero sign level of a strictly decreasing function is
    order-connected on an order-connected set. -/
theorem ordConnected_inter_sign_of_strictAnti {f : ℝ → ℝ} {s : Set ℝ}
    (hf : StrictAntiOn f s) (hs : s.OrdConnected) (t : SignType) (ht : t ≠ 0) :
    (s ∩ {x | SignType.sign (f x) = t}).OrdConnected := by
  constructor
  intro a ha c hc b hb
  have hbc := Set.mem_Icc.mp hb
  have hbS : b ∈ s := hs.out' ha.1 hc.1 hb
  refine ⟨hbS, ?_⟩
  have hfa := ha.2
  have hfc := hc.2
  have hab' := hf.antitoneOn ha.1 hbS hbc.1
  have hbc' := hf.antitoneOn hbS hc.1 hbc.2
  rcases SignType.trichotomy t with htneg | htzero | htpos
  · rw [htneg] at hfa hfc ⊢
    exact sign_eq_neg_one_iff.mpr (lt_of_le_of_lt hab' ((sign_eq_neg_one_iff.mp hfa)))
  · exact (ht htzero).elim
  · rw [htpos] at hfa hfc ⊢
    exact sign_eq_one_iff.mpr (lt_of_lt_of_le ((sign_eq_one_iff.mp hfc)) hbc')

/-- A nonzero constant sign level of a continuous function is open. -/
theorem isOpen_signLevel_of_ne_zero {f : ℝ → ℝ} (hf : Continuous f)
    {t : SignType} (ht : t ≠ 0) : IsOpen {x | SignType.sign (f x) = t} := by
  rcases SignType.trichotomy t with htneg | htzero | htpos
  · rw [htneg]
    have heq : {x | SignType.sign (f x) = -1} = f ⁻¹' Set.Iio 0 := by
      ext x
      simp [sign_eq_neg_one_iff]
    rw [heq]
    exact isOpen_Iio.preimage hf
  · exact (ht htzero).elim
  · rw [htpos]
    have heq : {x | SignType.sign (f x) = 1} = f ⁻¹' Set.Ioi 0 := by
      ext x
      simp [sign_eq_one_iff]
    rw [heq]
    exact isOpen_Ioi.preimage hf

end CollinsCAD
