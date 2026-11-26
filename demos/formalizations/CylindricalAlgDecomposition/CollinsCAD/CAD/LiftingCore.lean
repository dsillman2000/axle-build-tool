import Mathlib
import CAD.RealDelineabilityData
import CAD.Theorem4
import CAD.Pairwise

namespace CollinsCAD

open Polynomial MvPolynomial

/-- If every factor has nonzero fibres on a connected projection-invariant set,
    the factors are individually delineable and their product is delineable. -/
theorem exists_product_delineability_of_nonzero_fibers
    {dim : ℕ} (A : Finset (MvPolynomial (Fin (dim + 1)) ℝ))
    (S : Set (Fin dim → ℝ)) (hS : IsConnected S)
    (hproj : SignInvariant (collinsProj A) S)
    (hfiber : ∀ P ∈ A, ∀ a ∈ S, fiberPoly dim P a ≠ 0) :
    (∀ P ∈ A, IsRealDelineable P S) ∧
      IsRealDelineable (∏ P ∈ A, P) S := by
  classical
  obtain ⟨a₀, ha₀⟩ := hS.nonempty
  have hdata : ∀ P : A, Nonempty (RealDelineabilityData P.1 S) := by
    intro P
    have hprojP : SignInvariant (collinsProj {P.1}) S := by
      intro Q hQ
      exact hproj Q (collinsProj_mono (Finset.singleton_subset_iff.mpr P.2) hQ)
    rcases projection_theorem_4 P.1 S hS hprojP with hD | hzero
    · exact IsRealDelineable.nonempty_data hD
    · exact (hfiber P.1 P.2 a₀ ha₀ (hzero a₀ ha₀)).elim
  let W : (P : A) → RealDelineabilityData P.1 S := fun P => Classical.choice (hdata P)
  let Q : MvPolynomial (Fin (dim + 1)) ℝ := ∏ P ∈ A, P
  let R₀ : Finset ℝ := (fiberPoly dim Q a₀).roots.toFinset
  let b : (Σ P : A, Fin (W P).k) → (Fin dim → ℝ) → ℝ :=
    fun i => (W i.1).f i.2
  have hrep : ∀ r : R₀, ∃ i : Σ P : A, Fin (W P).k, b i a₀ = r := by
    intro r
    have hrroot : (fiberPoly dim Q a₀).IsRoot r :=
      Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp r.2)
    rcases (fiberPoly_eval_prod_eq_zero_iff A a₀ r).mp hrroot with ⟨P, hP, hxP⟩
    rcases (W ⟨P, hP⟩).exhaustive a₀ ha₀ r hxP with ⟨j, hj⟩
    exact ⟨⟨⟨P, hP⟩, j⟩, hj⟩
  let sel : R₀ → (Σ P : A, Fin (W P).k) := fun r => Classical.choose (hrep r)
  have hsel_base : ∀ r : R₀, b (sel r) a₀ = r := by
    intro r
    exact Classical.choose_spec (hrep r)
  let g : R₀ → (Fin dim → ℝ) → ℝ := fun r => b (sel r)
  have hraw : ∀ i j : (Σ P : A, Fin (W P).k),
      (∀ a ∈ S, b i a = b j a) ∨ (∀ a ∈ S, b i a ≠ b j a) := by
    intro i j
    exact projection_pairwise_disjoint_or_equal A S hS hproj i.1.2 j.1.2
      (W i.1).f (W j.1).f (RealDelineabilityData.branchFamily (W i.1))
      (RealDelineabilityData.branchFamily (W j.1)) i.2 j.2
  have hcoincidence : ∀ (i : Σ P : A, Fin (W P).k) (r : R₀)
      (a : Fin dim → ℝ) (ha : a ∈ S), (b i a = g r a) ↔ (b i a₀ = r) := by
    intro i r a ha
    rcases hraw i (sel r) with heq | hne
    · constructor
      · intro h
        exact (heq a₀ ha₀).trans (hsel_base r)
      · intro h
        exact heq a ha
    · constructor
      · intro h
        exact (hne a ha h).elim
      · intro h
        exact (hne a₀ ha₀ (h.trans (hsel_base r).symm)).elim
  have hg_ne : ∀ r s : R₀, r ≠ s → ∀ a ∈ S, g r a ≠ g s a := by
    intro r s hrs a ha
    rcases hraw (sel r) (sel s) with heq | hne
    · exfalso
      apply hrs
      apply Subtype.ext
      calc
        (r : ℝ) = b (sel r) a₀ := (hsel_base r).symm
        _ = b (sel s) a₀ := heq a₀ ha₀
        _ = (s : ℝ) := hsel_base s
    · exact hne a ha
  have hg_lt : ∀ r s : R₀, (r : ℝ) < (s : ℝ) → ∀ a ∈ S, g r a < g s a := by
    intro r s hrs a ha
    exact (lt_of_continuous_ne_of_base_lt hS.isPreconnected ha₀
      ((W (sel r).1).continuous (sel r).2)
      ((W (sel s).1).continuous (sel s).2)
      (hg_ne r s (ne_of_lt hrs))
      (by
        change b (sel r) a₀ < b (sel s) a₀
        rw [hsel_base r, hsel_base s]
        exact hrs)) a ha
  have hQne : ∀ a ∈ S, fiberPoly dim Q a ≠ 0 := by
    intro a ha
    rw [fiberPoly_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun P hP => hfiber P hP a ha)
  have hrootg : ∀ (r : R₀) (a : Fin dim → ℝ), a ∈ S →
      Polynomial.eval (g r a) (fiberPoly dim Q a) = 0 := by
    intro r a ha
    let i := sel r
    have hi := (W i.1).root_multiplicity i.2 a ha
    exact (fiberPoly_eval_prod_eq_zero_iff A a (g r a)).mpr
      ⟨i.1.1, i.1.2, hi.2.1⟩
  have hgcover : ∀ a ∈ S, ∀ x : ℝ,
      Polynomial.eval x (fiberPoly dim Q a) = 0 → ∃ r : R₀, g r a = x := by
    intro a ha x hx
    rcases (fiberPoly_eval_prod_eq_zero_iff A a x).mp hx with ⟨P, hP, hxP⟩
    rcases (W ⟨P, hP⟩).exhaustive a ha x hxP with ⟨j, hj⟩
    let i : Σ P : A, Fin (W P).k := ⟨⟨P, hP⟩, j⟩
    have hiroot := (W i.1).root_multiplicity i.2 a₀ ha₀
    have hirootprod : Polynomial.eval (b i a₀) (fiberPoly dim Q a₀) = 0 :=
      (fiberPoly_eval_prod_eq_zero_iff A a₀ (b i a₀)).mpr
        ⟨P, hP, hiroot.2.1⟩
    have himem : b i a₀ ∈ R₀ :=
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hQne a₀ ha₀)).mpr hirootprod)
    let r : R₀ := ⟨b i a₀, himem⟩
    have hb := (hcoincidence i r a ha).mpr rfl
    exact ⟨r, hb.symm.trans hj⟩
  let E : R₀ → ℕ := fun r => Polynomial.rootMultiplicity (r : ℝ) (fiberPoly dim Q a₀)
  have hEpos : ∀ r : R₀, 0 < E r := by
    intro r
    dsimp [E]
    exact (Polynomial.rootMultiplicity_pos (hQne a₀ ha₀)).mpr
      (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp r.2))
  have hfactor_mult : ∀ (P : MvPolynomial (Fin (dim + 1)) ℝ) (hP : P ∈ A)
      (r : R₀) (a : Fin dim → ℝ), a ∈ S →
      Polynomial.rootMultiplicity (g r a) (fiberPoly dim P a) =
        Polynomial.rootMultiplicity (r : ℝ) (fiberPoly dim P a₀) := by
    intro P hP r a ha
    by_cases hr : Polynomial.eval (r : ℝ) (fiberPoly dim P a₀) = 0
    · rcases (W ⟨P, hP⟩).exhaustive a₀ ha₀ (r : ℝ) hr with ⟨j, hj⟩
      let i : Σ P : A, Fin (W P).k := ⟨⟨P, hP⟩, j⟩
      have hb := (hcoincidence i r a ha).mpr (by exact hj)
      have hbaseMult : Polynomial.rootMultiplicity (b i a₀) (fiberPoly dim P a₀) =
          (W i.1).e i.2 := ((W i.1).root_multiplicity i.2 a₀ ha₀).2.2
      calc
        Polynomial.rootMultiplicity (g r a) (fiberPoly dim P a) =
            Polynomial.rootMultiplicity (b i a) (fiberPoly dim P a) := by rw [hb]
        _ = (W i.1).e i.2 := ((W i.1).root_multiplicity i.2 a ha).2.2
        _ = Polynomial.rootMultiplicity (r : ℝ) (fiberPoly dim P a₀) := by
          rw [← hj]
          exact hbaseMult.symm
    · have hgnot : ¬ (fiberPoly dim P a).IsRoot (g r a) := by
        intro hx
        rcases (W ⟨P, hP⟩).exhaustive a ha (g r a) hx with ⟨j, hj⟩
        let i : Σ P : A, Fin (W P).k := ⟨⟨P, hP⟩, j⟩
        have hb := (hcoincidence i r a ha).mp hj
        have hiroot : Polynomial.eval (b i a₀) (fiberPoly dim P a₀) = 0 :=
          ((W i.1).root_multiplicity i.2 a₀ ha₀).2.1
        rw [hb] at hiroot
        exact hr hiroot
      rw [Polynomial.rootMultiplicity_eq_zero hgnot,
        Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot.def] using hr)]
  have hmult : ∀ (r : R₀) (a : Fin dim → ℝ), a ∈ S →
      Polynomial.rootMultiplicity (g r a) (fiberPoly dim Q a) = E r := by
    intro r a ha
    calc
      Polynomial.rootMultiplicity (g r a) (fiberPoly dim Q a) =
          ∑ P ∈ A, Polynomial.rootMultiplicity (g r a) (fiberPoly dim P a) :=
        rootMultiplicity_fiberPoly_prod A a (fun P hP => hfiber P hP a ha) (g r a)
      _ = ∑ P ∈ A, Polynomial.rootMultiplicity (r : ℝ) (fiberPoly dim P a₀) := by
        apply Finset.sum_congr rfl
        intro P hP
        exact hfactor_mult P hP r a ha
      _ = E r := (rootMultiplicity_fiberPoly_prod A a₀
        (fun P hP => hfiber P hP a₀ ha₀) (r : ℝ)).symm
  let k := R₀.card
  let ord : Fin k ↪o ℝ := R₀.orderEmbOfFin rfl
  let ordR : Fin k → R₀ := fun i =>
    ⟨ord i, R₀.orderEmbOfFin_mem rfl i⟩
  let f : Fin k → (Fin dim → ℝ) → ℝ := fun i => g (ordR i)
  let e : Fin k → ℕ := fun i => E (ordR i)
  have hD : IsRealDelineable Q S := by
    refine ⟨k, f, e, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (W (sel (ordR i)).1).continuous (sel (ordR i)).2
    · intro i a ha
      exact ⟨hEpos (ordR i), hrootg (ordR i) a ha, hmult (ordR i) a ha⟩
    · intro a ha x hx
      rcases hgcover a ha x hx with ⟨r, hr⟩
      rcases (R₀.orderIsoOfFin rfl).surjective r with ⟨i, hi⟩
      have hiR : ordR i = r := by
        apply Subtype.ext
        simpa only [ordR, ord, Finset.coe_orderIsoOfFin_apply] using
          congrArg Subtype.val hi
      exact ⟨i, by simpa [f, hiR] using hr⟩
    · intro i j a ha hij
      exact hg_lt (ordR i) (ordR j) (ord.strictMono hij) a ha
  refine ⟨?_, hD⟩
  intro P hP
  exact (RealDelineabilityData.isRealDelineable (W ⟨P, hP⟩))

end CollinsCAD
