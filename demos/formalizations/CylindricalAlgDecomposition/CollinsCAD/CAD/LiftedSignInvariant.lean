import Mathlib
import CAD.CylinderPartition
import CAD.ZeroFiber

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- The lifting data needed on one connected base cell. -/
structure LiftingWitness {r : ℕ}
    (A : Finset (MvPolynomial (Fin (r + 1)) ℝ)) (S : Cell r) where
  retained : Finset (MvPolynomial (Fin (r + 1)) ℝ)
  retained_subset : retained ⊆ A
  roots : RootFamily S.carrier
  retained_or_zero : ∀ P ∈ A,
    P ∈ retained ∨ (∀ a ∈ S.carrier, fiberPoly r P a = 0)
  exhaustive : ∀ a ∈ S.carrier, ∀ x : ℝ,
    (∃ P ∈ retained, Polynomial.eval x (fiberPoly r P a) = 0) →
      ∃ i, roots.f i a = x
  dichotomy : ∀ P ∈ retained, ∀ i,
    (∀ a ∈ S.carrier, Polynomial.eval (roots.f i a) (fiberPoly r P a) = 0) ∨
    (∀ a ∈ S.carrier, Polynomial.eval (roots.f i a) (fiberPoly r P a) ≠ 0)
  section_root : ∀ i a, a ∈ S.carrier →
    ∃ P ∈ retained, Polynomial.eval (roots.f i a) (fiberPoly r P a) = 0

/-- Non-section lifted-cell shapes. -/
inductive SectorShape (S : Cell r) (R : RootFamily S.carrier) : Cell (r + 1) → Prop where
  | whole (hk : R.k = 0) : SectorShape S R (Cell.whole S)
  | lower (i : Fin R.k) (hi : i.val = 0) :
      SectorShape S R (Cell.lower S (R.f i) (R.continuous i))
  | bounded (i j : Fin R.k) (hj : j.val = i.val + 1) :
      SectorShape S R (Cell.bounded S (R.f i) (R.f j)
        (R.continuous i) (R.continuous j)
        (fun a ha => R.ordered i j a ha (by
          change i.val < j.val
          omega)))
  | upper (i : Fin R.k) (hi : i.val + 1 = R.k) :
      SectorShape S R (Cell.upper S (R.f i) (R.continuous i))

/-- Package lifting data for a family whose fibres are already nonzero. -/
theorem exists_liftingWitness_of_nonzero_fibers
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} (S : Cell r)
    (hproj : SignInvariant (collinsProj A) S.carrier)
    (hfiber : ∀ P ∈ A, ∀ a ∈ S.carrier, fiberPoly r P a ≠ 0) :
    Nonempty (LiftingWitness A S) := by
  classical
  rcases projection_fundamental_lifting A S.carrier S.connected hproj hfiber with
    ⟨hDall, k, f, e, hcont, hroot, hexhaust, hmono, hdich, hrange⟩
  let R : RootFamily S.carrier := ⟨k, f, hcont, hmono⟩
  refine ⟨⟨A, fun _ h => h, R, ?_, ?_, hdich, ?_⟩⟩
  · intro P hP
    exact Or.inl hP
  · intro a ha x hx
    rcases hx with ⟨P, hP, hxP⟩
    have hxprod : Polynomial.eval x
        (fiberPoly r (∏ Q ∈ A, Q) a) = 0 :=
      (fiberPoly_eval_prod_eq_zero_iff A a x).mpr ⟨P, hP, hxP⟩
    exact hexhaust a ha x hxprod
  · intro i a ha
    have hxprod := (hroot i a ha).2.1
    rcases (fiberPoly_eval_prod_eq_zero_iff A a (f i a)).mp hxprod with ⟨P, hP, hxP⟩
    exact ⟨P, hP, hxP⟩

/-- Package projection-invariant lifting data after removing zero fibres. -/
theorem exists_liftingWitness_of_signInvariant_proj
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} (S : Cell r)
    (hproj : SignInvariant (collinsProj A) S.carrier) :
    Nonempty (LiftingWitness A S) := by
  classical
  let G := nonzeroFibers A S.sample
  have hfiber : ∀ P ∈ G, ∀ a ∈ S.carrier, fiberPoly r P a ≠ 0 := by
    intro P hP
    exact fiberPoly_ne_zero_of_mem_nonzeroFibers S.sample_mem hproj hP
  have hprojG : SignInvariant (collinsProj G) S.carrier :=
    signInvariant_collinsProj_nonzeroFibers S.sample hproj
  rcases projection_fundamental_lifting G S.carrier S.connected hprojG hfiber with
    ⟨hDall, k, f, e, hcont, hroot, hexhaust, hmono, hdich, hrange⟩
  let R : RootFamily S.carrier := ⟨k, f, hcont, hmono⟩
  refine ⟨⟨G, nonzeroFibers_subset A S.sample, R, ?_, ?_, hdich, ?_⟩⟩
  · intro P hP
    by_cases hG : P ∈ G
    · exact Or.inl hG
    · exact Or.inr (fiberPoly_eq_zero_of_not_mem_nonzeroFibers
        S.sample_mem hproj hP hG)
  · intro a ha x hx
    rcases hx with ⟨P, hP, hxP⟩
    have hxprod : Polynomial.eval x
        (fiberPoly r (∏ Q ∈ G, Q) a) = 0 :=
      (fiberPoly_eval_prod_eq_zero_iff G a x).mpr ⟨P, hP, hxP⟩
    exact hexhaust a ha x hxprod
  · intro i a ha
    have hxprod := (hroot i a ha).2.1
    rcases (fiberPoly_eval_prod_eq_zero_iff G a (f i a)).mp hxprod with ⟨P, hP, hxP⟩
    exact ⟨P, hP, hxP⟩

/-- Sector shapes are lifted-cell shapes. -/
theorem SectorShape.toLiftShape {S : Cell r} {R : RootFamily S.carrier}
    {c : Cell (r + 1)} (h : SectorShape S R c) : LiftShape S R c := by
  cases h with
  | whole hk => exact .whole hk
  | lower i hi => exact .lower i hi
  | bounded i j hj => exact .bounded i j hj
  | upper i hi => exact .upper i hi

/-- A retained factor has no root in a sector. -/
theorem SectorShape.not_root {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {S : Cell r} (W : LiftingWitness A S) {c : Cell (r + 1)}
    (hc : SectorShape S W.roots c)
    {P : MvPolynomial (Fin (r + 1)) ℝ} (hP : P ∈ W.retained)
    {z : Fin (r + 1) → ℝ} (hz : z ∈ c.carrier) :
    MvPolynomial.eval z P ≠ 0 := by
  intro hzero
  have hfiber : Polynomial.eval (z (Fin.last r))
      (fiberPoly r P (Fin.init z)) = 0 := by
    simpa [fiberPoly_eval] using hzero
  rcases W.exhaustive (Fin.init z)
      (LiftShape.init_mem (SectorShape.toLiftShape hc) hz)
    (z (Fin.last r)) ⟨P, hP, hfiber⟩ with ⟨l, hl⟩
  cases hc with
  | whole hk =>
    have hk0 : W.roots.k = 0 := hk
    exact Fin.elim0 (by simpa [hk0] using l)
  | lower j hj =>
    have hmem := Cell.mem_lower.mp hz
    by_cases hjl : j = l
    · subst l
      linarith [hmem.2, hl]
    · have hjl' : j < l := by
        apply Fin.val_fin_lt.mpr
        omega
      have hord := W.roots.ordered j l (Fin.init z) hmem.1 hjl'
      linarith [hmem.2, hl]
  | bounded a b hab =>
    have hmem := Cell.mem_bounded.mp hz
    by_cases hal : a = l
    · subst l
      linarith [hmem.2.1, hl]
    · by_cases hbl : b = l
      · subst l
        linarith [hmem.2.2, hl]
      · have hsplit : l < a ∨ b < l := by
          by_contra hnot
          push Not at hnot
          have hla : a ≤ l := hnot.1
          have hlb : l ≤ b := hnot.2
          have hv1 := Fin.le_iff_val_le_val.mp hla
          have hv2 := Fin.le_iff_val_le_val.mp hlb
          have hlne_a : l.val ≠ a.val := fun heq => hal (Fin.ext heq.symm)
          have hlne_b : l.val ≠ b.val := fun heq => hbl (Fin.ext heq.symm)
          omega
        rcases hsplit with hla | hbl
        · have hord := W.roots.ordered l a (Fin.init z) hmem.1 hla
          linarith [hmem.2.1, hl]
        · have hord := W.roots.ordered b l (Fin.init z) hmem.1 hbl
          linarith [hmem.2.2, hl]
  | upper j hj =>
    have hmem := Cell.mem_upper.mp hz
    by_cases hjl : j = l
    · subst l
      linarith [hmem.2, hl]
    · have hlj : l ≤ j := by
        apply Fin.le_iff_val_le_val.mpr
        have hlval := l.isLt
        omega
      have hlj' : l < j := lt_of_le_of_ne hlj (Ne.symm hjl)
      have hord := W.roots.ordered l j (Fin.init z) hmem.1 hlj'
      linarith [hmem.2, hl]

/-- Every lifted cell is sign-invariant for the original family. -/
theorem LiftShape.signInvariant {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {S : Cell r} (W : LiftingWitness A S) {c : Cell (r + 1)}
    (hc : LiftShape S W.roots c) : SignInvariant A c.carrier := by
  intro P hP
  have hconn := c.connected
  rcases W.retained_or_zero P hP with hret | hzero
  · cases hc with
    | whole hk =>
      apply SignInvariantPoly.of_connected_ne_zero hconn
      intro z hz
      exact SectorShape.not_root W (.whole hk) hret hz
    | lower i hi =>
      apply SignInvariantPoly.of_connected_ne_zero hconn
      intro z hz
      exact SectorShape.not_root W (.lower i hi) hret hz
    | graph i =>
      rcases W.dichotomy P hret i with hzero' | hne
      · apply SignInvariantPoly.of_eq_zero
        intro z hz
        have hmem := Cell.mem_graph.mp hz
        have hfib : Polynomial.eval (z (Fin.last r))
            (fiberPoly r P (Fin.init z)) = 0 := by
          simpa [hmem.2] using hzero' (Fin.init z) hmem.1
        simpa [fiberPoly_eval] using hfib
      · apply SignInvariantPoly.of_connected_ne_zero hconn
        intro z hz hzero
        have hmem := Cell.mem_graph.mp hz
        have hfib : Polynomial.eval (z (Fin.last r))
            (fiberPoly r P (Fin.init z)) ≠ 0 := by
          simpa [hmem.2] using hne (Fin.init z) hmem.1
        exact hfib (by simpa [fiberPoly_eval] using hzero)
    | bounded i j hj =>
      apply SignInvariantPoly.of_connected_ne_zero hconn
      intro z hz
      exact SectorShape.not_root W (.bounded i j hj) hret hz
    | upper i hi =>
      apply SignInvariantPoly.of_connected_ne_zero hconn
      intro z hz
      exact SectorShape.not_root W (.upper i hi) hret hz
  · apply SignInvariantPoly.of_eq_zero
    intro z hz
    have hp0 : fiberPoly r P (Fin.init z) = 0 :=
      hzero (Fin.init z) (LiftShape.init_mem hc hz)
    calc
      MvPolynomial.eval z P =
          MvPolynomial.eval (Fin.snoc (Fin.init z) (z (Fin.last r))) P := by
        rw [Fin.snoc_init_self]
      _ = Polynomial.eval (z (Fin.last r)) (fiberPoly r P (Fin.init z)) :=
        (fiberPoly_eval r P (Fin.init z) (z (Fin.last r))).symm
      _ = 0 := by rw [hp0, Polynomial.eval_zero]

/-- Construct an invariant canonical cylinder on a projection-invariant cell. -/
theorem exists_cylinder_of_signInvariant_proj
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)} (S : Cell r)
    (hproj : SignInvariant (collinsProj A) S.carrier) :
    ∃ L : Cylinder r, L.parent = S ∧ IsCylinderPartition L ∧
      ∀ c ∈ L.children, SignInvariant A c.carrier := by
  classical
  obtain ⟨W⟩ := exists_liftingWitness_of_signInvariant_proj S hproj
  have hinv : ∀ c ∈ liftCells S W.roots, SignInvariant A c.carrier := by
    intro c hc
    exact LiftShape.signInvariant W (liftCells_shape S W.roots c hc)
  have hsection : ∀ i a, a ∈ S.carrier →
      ∃ P ∈ A, Polynomial.eval (W.roots.f i a) (fiberPoly r P a) = 0 := by
    intro i a ha
    rcases W.section_root i a ha with ⟨P, hP, hroot⟩
    exact ⟨P, W.retained_subset hP, hroot⟩
  let L := Cylinder.canonical S W.roots A hinv hsection
  refine ⟨L, rfl, IsCylinderPartition.canonical S W.roots A hinv hsection, ?_⟩
  intro c hc
  exact L.invariant c hc

end CollinsCAD
