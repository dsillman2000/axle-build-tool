import Mathlib
import Analysis.ThomLemma

namespace CollinsCAD

open Polynomial

/-- Simultaneous derivative sign conditions for a finite polynomial family. -/
def familyDerivativeSignCell (A : Finset (Polynomial ℝ))
    (σ : Polynomial ℝ → ℕ → SignType) : Set ℝ :=
  {x | ∀ P ∈ A, ∀ k ≤ P.natDegree, derivativeSignVector P x k = σ P k}

/-- Equality of all derivative signs for a finite family. -/
def SameDerivativeSigns (A : Finset (Polynomial ℝ)) (x y : ℝ) : Prop :=
  ∀ P ∈ A, ∀ k ≤ P.natDegree,
    derivativeSignVector P x k = derivativeSignVector P y k

/-- A root of a family lies between two points. -/
def RootSeparatedByFamily (A : Finset (Polynomial ℝ)) (x y : ℝ) : Prop :=
  ∃ z, (x ≤ z ∧ z ≤ y ∨ y ≤ z ∧ z ≤ x) ∧ ∃ P ∈ A, P.eval z = 0

private theorem emptyOrSingleton_inter' {s t : Set ℝ}
    (hs : EmptyOrSingleton s) : EmptyOrSingleton (t ∩ s) := by
  simpa [Set.inter_comm] using emptyOrSingleton_inter (s := s) (t := t) hs

/-- Family Thom-lemma classification. -/
theorem familyDerivativeSignCell_classification
    (A : Finset (Polynomial ℝ)) (hA : ∀ P ∈ A, P ≠ 0)
    (σ : Polynomial ℝ → ℕ → SignType) :
    ((∃ P ∈ A, HasZeroSign P (σ P)) →
      EmptyOrSingleton (familyDerivativeSignCell A σ)) ∧
    ((∀ P ∈ A, ¬ HasZeroSign P (σ P)) →
      EmptyOrOpenInterval (familyDerivativeSignCell A σ)) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have hcell : familyDerivativeSignCell ∅ σ = Set.univ := by
      ext x
      simp [familyDerivativeSignCell]
    rw [hcell]
    constructor
    · rintro ⟨P, hP⟩
      simp at hP
    · intro _
      exact Or.inr ⟨Set.univ_nonempty, isOpen_univ, Set.ordConnected_univ⟩
  | @insert P A hP ih =>
    have hA' : ∀ Q ∈ A, Q ≠ 0 :=
      fun Q hQ => hA Q (Finset.mem_insert_of_mem hQ)
    have htail := ih hA'
    have hPclass := derivativeSignCell_classification P
      (hA P (Finset.mem_insert_self P A)) (σ P)
    have hcell : familyDerivativeSignCell (insert P A) σ =
        derivativeSignCell P (σ P) ∩ familyDerivativeSignCell A σ := by
      ext x
      simp only [familyDerivativeSignCell, Set.mem_ofPred_eq,
        Finset.mem_insert, forall_eq_or_imp]
      aesop
    have hzero : (∃ Q ∈ insert P A, HasZeroSign Q (σ Q)) ↔
        HasZeroSign P (σ P) ∨ ∃ Q ∈ A, HasZeroSign Q (σ Q) := by
      constructor
      · rintro ⟨Q, hQ, hz⟩
        rcases Finset.mem_insert.mp hQ with rfl | hQ
        · exact Or.inl hz
        · exact Or.inr ⟨Q, hQ, hz⟩
      · rintro (hz | ⟨Q, hQ, hz⟩)
        · exact ⟨P, Finset.mem_insert_self P A, hz⟩
        · exact ⟨Q, Finset.mem_insert_of_mem hQ, hz⟩
    rw [hcell]
    constructor
    · intro hz
      rcases hzero.mp hz with hPz | hAz
      · exact emptyOrSingleton_inter (hPclass.1 hPz)
      · exact emptyOrSingleton_inter' (htail.1 hAz)
    · intro hz
      have hPz : ¬ HasZeroSign P (σ P) := hz P (by simp)
      have hAz : ∀ Q ∈ A, ¬ HasZeroSign Q (σ Q) :=
        fun Q hQ => hz Q (by simp [hQ])
      exact emptyOrOpenInterval_inter (hPclass.2 hPz) (htail.2 hAz)

/-- Equal family derivative signs cannot cross a family root. -/
theorem eq_of_rootSeparatedByFamily_of_sameDerivativeSigns
    {A : Finset (Polynomial ℝ)} (hA : ∀ P ∈ A, P ≠ 0)
    {x y : ℝ} (hsep : RootSeparatedByFamily A x y)
    (hs : SameDerivativeSigns A x y) : x = y := by
  classical
  let σ : Polynomial ℝ → ℕ → SignType := fun P => derivativeSignVector P x
  have hx : x ∈ familyDerivativeSignCell A σ := by
    intro P hP k hk
    rfl
  have hy : y ∈ familyDerivativeSignCell A σ := by
    intro P hP k hk
    exact (hs P hP k hk).symm
  rcases familyDerivativeSignCell_classification A hA σ with ⟨hzero, hnonzero⟩
  by_cases hz : ∃ P ∈ A, HasZeroSign P (σ P)
  · rcases hzero hz with hempty | ⟨a, hsingle⟩
    · rw [hempty] at hx
      exact hx.elim
    · rw [hsingle] at hx hy
      exact hx.trans hy.symm
  · have hz' : ∀ P ∈ A, ¬ HasZeroSign P (σ P) :=
      fun P hP h => hz ⟨P, hP, h⟩
    have hclass := hnonzero hz'
    rcases hclass with hempty | hopen
    · rw [hempty] at hx
      exact hx.elim
    · rcases hsep with ⟨z, hbetween, Q, hQ, hzroot⟩
      have hzcell : z ∈ familyDerivativeSignCell A σ := by
        rcases hbetween with ⟨hxz, hzy⟩ | ⟨hyz, hzx⟩
        · exact hopen.2.2.out' hx hy ⟨hxz, hzy⟩
        · exact hopen.2.2.out' hy hx ⟨hyz, hzx⟩
      have hzsign := hzcell Q hQ 0 (Nat.zero_le _)
      change SignType.sign ((iteratedDerivative Q 0).eval z) = σ Q 0 at hzsign
      rw [iteratedDerivative_zero, hzroot] at hzsign
      have hsign0 : SignType.sign (0 : ℝ) = 0 := (sign_eq_zero_iff).mpr rfl
      rw [hsign0] at hzsign
      have hQnon : ¬ HasZeroSign Q (σ Q) := hz' Q hQ
      exact (hQnon ⟨0, Nat.zero_le _, hzsign.symm⟩).elim

end CollinsCAD
