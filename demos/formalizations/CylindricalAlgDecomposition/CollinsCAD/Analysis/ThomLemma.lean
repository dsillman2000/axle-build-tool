import Mathlib
import Analysis.ThomCells

namespace CollinsCAD

open Polynomial

/-- Constant nonzero polynomials have the expected Thom-cell classification. -/
theorem constant_classification (P : Polynomial ℝ) (hP : P ≠ 0)
    (hdeg : P.natDegree = 0) (σ : ℕ → SignType) :
    (HasZeroSign P σ → EmptyOrSingleton (derivativeSignCell P σ)) ∧
    (¬ HasZeroSign P σ → EmptyOrOpenInterval (derivativeSignCell P σ)) := by
  have hC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hc : P.coeff 0 ≠ 0 := by
    intro hz
    apply hP
    rw [hC, hz, Polynomial.C_0]
  have hcell : derivativeSignCell P σ = {x : ℝ | SignType.sign (P.coeff 0) = σ 0} := by
    ext x
    have heval : P.eval x = P.coeff 0 := by
      calc
        P.eval x = (Polynomial.C (P.coeff 0)).eval x :=
          congrArg (fun q : Polynomial ℝ => q.eval x) hC
        _ = P.coeff 0 := by simp
    constructor
    · intro hx
      have hx0 := hx 0 (by simp [hdeg])
      change SignType.sign ((iteratedDerivative P 0).eval x) = σ 0 at hx0
      rw [iteratedDerivative_zero, heval] at hx0
      exact hx0
    · intro hx k hk
      have hk0 : k = 0 := by omega
      subst k
      change SignType.sign ((iteratedDerivative P 0).eval x) = σ 0
      rw [iteratedDerivative_zero, heval]
      exact hx
  have hzero : HasZeroSign P σ ↔ σ 0 = 0 := by
    constructor
    · rintro ⟨k, hk, hσ⟩
      have hk0 : k = 0 := by omega
      subst k
      exact hσ
    · intro hσ
      exact ⟨0, by simp [hdeg], hσ⟩
  rw [hcell]
  constructor
  · intro hz
    have hs0 : σ 0 = 0 := hzero.mp hz
    left
    ext x
    simp [hs0, sign_eq_zero_iff, hc]
  · intro hz
    rcases SignType.trichotomy (σ 0) with hneg | hzero' | hpos
    · by_cases hcneg : P.coeff 0 < 0
      · have hset : {x : ℝ | SignType.sign (P.coeff 0) = -1} = Set.univ := by
          ext x
          simp [hcneg]
        rw [hneg, hset]
        exact Or.inr ⟨Set.univ_nonempty, isOpen_univ, Set.ordConnected_univ⟩
      · have hcpos : 0 < P.coeff 0 :=
          lt_of_le_of_ne (le_of_not_gt hcneg) (Ne.symm hc)
        have hset : {x : ℝ | SignType.sign (P.coeff 0) = -1} = ∅ := by
          ext x
          simp [hcpos]
        rw [hneg, hset]
        exact Or.inl rfl
    · exact (hz (hzero.mpr hzero')).elim
    · by_cases hcpos : 0 < P.coeff 0
      · have hset : {x : ℝ | SignType.sign (P.coeff 0) = 1} = Set.univ := by
          ext x
          simp [hcpos]
        rw [hpos, hset]
        exact Or.inr ⟨Set.univ_nonempty, isOpen_univ, Set.ordConnected_univ⟩
      · have hcneg : P.coeff 0 < 0 :=
          lt_of_le_of_ne (le_of_not_gt hcpos) hc
        have hset : {x : ℝ | SignType.sign (P.coeff 0) = 1} = ∅ := by
          ext x
          simp [hcneg]
        rw [hpos, hset]
        exact Or.inl rfl

/-- Bounded-degree induction for the derivative-sign classification. -/
theorem derivativeSignCell_classification_aux (n : ℕ) :
    ∀ P : Polynomial ℝ, P ≠ 0 → P.natDegree ≤ n → ∀ σ : ℕ → SignType,
      (HasZeroSign P σ → EmptyOrSingleton (derivativeSignCell P σ)) ∧
      (¬ HasZeroSign P σ → EmptyOrOpenInterval (derivativeSignCell P σ)) := by
  induction n with
  | zero =>
    intro P hP hdeg σ
    exact constant_classification P hP (by omega) σ
  | succ n ih =>
    intro P hP hdeg σ
    by_cases hP0 : P.natDegree = 0
    · exact constant_classification P hP hP0 σ
    · let Q := P.derivative
      let τ : ℕ → SignType := fun k => σ (k + 1)
      let T := derivativeSignCell Q τ
      have hQ : Q ≠ 0 := Polynomial.derivative_ne_zero.mpr hP0
      have hQdeg : Q.natDegree = P.natDegree - 1 := by simp [Q]
      have hQle : Q.natDegree ≤ n := by omega
      have htail := ih Q hQ hQle τ
      have hcell : derivativeSignCell P σ =
          T ∩ {x | SignType.sign (P.eval x) = σ 0} := by
        ext x
        constructor
        · intro hx
          refine ⟨?_, ?_⟩
          · intro k hk
            exact hx (k + 1) (by omega)
          · simpa [derivativeSignVector, iteratedDerivative] using hx 0 (Nat.zero_le _)
        · rintro ⟨ht, h0⟩ k hk
          cases k with
          | zero => simpa [derivativeSignVector, iteratedDerivative] using h0
          | succ k => exact ht k (by omega)
      have htail_zero : HasZeroSign Q τ ↔
          ∃ k, 1 ≤ k ∧ k ≤ P.natDegree ∧ σ k = 0 := by
        constructor
        · rintro ⟨k, hk, hσ⟩
          exact ⟨k + 1, by omega, by omega, hσ⟩
        · rintro ⟨k, hk1, hkP, hσ⟩
          refine ⟨k - 1, by omega, ?_⟩
          change σ ((k - 1) + 1) = 0
          rw [Nat.sub_add_cancel hk1]
          exact hσ
      have hQsign : ∀ x ∈ T, SignType.sign (Q.eval x) = σ 1 := by
        intro x hx
        simpa [derivativeSignVector, iteratedDerivative, Q, τ] using hx 0 (Nat.zero_le _)
      have hstrict_of_no_zero (htz : ¬ HasZeroSign Q τ) :
          StrictMonoOn (fun x => P.eval x) T ∨
            StrictAntiOn (fun x => P.eval x) T := by
        have hTconv := convex_of_emptyOrOpenInterval (htail.2 htz)
        have hσ1 : σ 1 ≠ 0 := by
          intro hzero
          exact htz (htail_zero.mpr ⟨1, by omega, by omega, hzero⟩)
        have hcont : Continuous (fun x => P.eval x) := P.continuous
        have hderiv : ∀ x, deriv (fun y => P.eval y) x = Q.eval x := by
          intro x
          exact (Polynomial.hasDerivAt P x).deriv
        rcases SignType.trichotomy (σ 1) with hneg | hzero | hpos
        · right
          apply strictAntiOn_of_deriv_neg hTconv hcont.continuousOn
          intro x hx
          rw [hderiv]
          have hs := hQsign x (interior_subset hx)
          rw [hneg] at hs
          exact sign_eq_neg_one_iff.mp hs
        · exact (hσ1 hzero).elim
        · left
          apply strictMonoOn_of_deriv_pos hTconv hcont.continuousOn
          intro x hx
          rw [hderiv]
          have hs := hQsign x (interior_subset hx)
          rw [hpos] at hs
          exact sign_eq_one_iff.mp hs
      constructor
      · intro hz
        rw [hcell]
        by_cases htz : HasZeroSign Q τ
        · exact emptyOrSingleton_inter (htail.1 htz)
        · have hσ0 : σ 0 = 0 := by
            rcases hz with ⟨k, hk, hσ⟩
            cases k with
            | zero => exact hσ
            | succ k => exact (htz (htail_zero.mpr ⟨k + 1, by omega, by omega, hσ⟩)).elim
          have heq : {x | SignType.sign (P.eval x) = σ 0} =
              {x | P.eval x = 0} := by
            ext x
            simp [hσ0, sign_eq_zero_iff]
          rw [heq]
          exact strictOn_root_emptyOrSingleton (hstrict_of_no_zero htz)
      · intro hz
        have htz : ¬ HasZeroSign Q τ := by
          intro h
          rcases htail_zero.mp h with ⟨k, hk1, hkP, hσ⟩
          exact hz ⟨k, hkP, hσ⟩
        have hσ0 : σ 0 ≠ 0 := by
          intro hσ
          exact hz ⟨0, Nat.zero_le _, hσ⟩
        have hTopen := isOpen_of_emptyOrOpenInterval (htail.2 htz)
        have hTord : T.OrdConnected := by
          rcases htail.2 htz with hT | hT
          · have hT' : T = ∅ := hT
            rw [hT']
            exact Set.ordConnected_empty
          · exact hT.2.2
        rw [hcell]
        by_cases hne : (T ∩ {x | SignType.sign (P.eval x) = σ 0}).Nonempty
        · right
          refine ⟨hne, hTopen.inter (isOpen_signLevel_of_ne_zero P.continuous hσ0), ?_⟩
          rcases hstrict_of_no_zero htz with hmono | hanti
          · exact ordConnected_inter_sign_of_strictMono hmono hTord (σ 0) hσ0
          · exact ordConnected_inter_sign_of_strictAnti hanti hTord (σ 0) hσ0
        · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

/-- Refined Thom-lemma classification. -/
theorem derivativeSignCell_classification
    (P : Polynomial ℝ) (hP : P ≠ 0) (σ : ℕ → SignType) :
    (HasZeroSign P σ → EmptyOrSingleton (derivativeSignCell P σ)) ∧
    (¬ HasZeroSign P σ → EmptyOrOpenInterval (derivativeSignCell P σ)) :=
  derivativeSignCell_classification_aux P.natDegree P hP le_rfl σ

/-- Thom's lemma for the full derivative sign vector. -/
theorem thom_lemma_univariate (P : Polynomial ℝ) (hP : P ≠ 0)
    (σ : ℕ → SignType) : IsThomCell (derivativeSignCell P σ) := by
  rcases derivativeSignCell_classification P hP σ with ⟨hzero, hnonzero⟩
  by_cases hz : HasZeroSign P σ
  · rcases hzero hz with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hnonzero hz with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

end CollinsCAD
