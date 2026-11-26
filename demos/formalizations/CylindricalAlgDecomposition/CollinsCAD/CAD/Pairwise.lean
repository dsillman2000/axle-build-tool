import Mathlib
import CAD.EffectiveFamily
import CAD.EffectiveReductum
import CAD.RootBranchCoincidence
import Analysis.MonicComplexFiber

namespace CollinsCAD

open Polynomial MvPolynomial

/-- A continuous family of real root branches for a polynomial with nonzero
    fibres on the base set. -/
def IsRealRootBranchFamily {r k : ℕ}
    (P : MvPolynomial (Fin (r + 1)) ℝ) (S : Set (Fin r → ℝ))
    (f : Fin k → (Fin r → ℝ) → ℝ) : Prop :=
  (∀ a ∈ S, fiberPoly r P a ≠ 0) ∧
  (∀ i, ContinuousOn (f i) S) ∧
  (∀ i a, a ∈ S → Polynomial.eval (f i a) (fiberPoly r P a) = 0)

/-- Monic complex normalization preserves GCD degree. -/
theorem gcdNatDegree_monicComplexFiber {X : Type*}
    (q₁ q₂ : X → Polynomial ℝ) (d₁ d₂ : ℕ) (x : X)
    (h₁ : (q₁ x).coeff d₁ ≠ 0) (h₂ : (q₂ x).coeff d₂ ≠ 0) :
    gcdNatDegree (monicComplexFiber q₁ d₁ x) (monicComplexFiber q₂ d₂ x) =
      gcdNatDegree ((q₁ x).map (algebraMap ℝ ℂ))
        ((q₂ x).map (algebraMap ℝ ℂ)) := by
  have hq₁neR : q₁ x ≠ 0 := by
    intro hz
    apply h₁
    have hc := congrArg (fun q : Polynomial ℝ => q.coeff d₁) hz
    simpa using hc
  have hq₂neR : q₂ x ≠ 0 := by
    intro hz
    apply h₂
    have hc := congrArg (fun q : Polynomial ℝ => q.coeff d₂) hz
    simpa using hc
  have hq₁ne : (q₁ x).map (algebraMap ℝ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hq₁neR
  have hq₂ne : (q₂ x).map (algebraMap ℝ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hq₂neR
  have hc₁ : (algebraMap ℝ ℂ ((q₁ x).coeff d₁))⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr h₁)
  have hc₂ : (algebraMap ℝ ℂ ((q₂ x).coeff d₂))⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr h₂)
  have hq₁scaled : (q₁ x).map (algebraMap ℝ ℂ) *
      Polynomial.C ((algebraMap ℝ ℂ ((q₁ x).coeff d₁))⁻¹) ≠ 0 :=
    mul_ne_zero hq₁ne (by simpa using hc₁)
  calc
    gcdNatDegree (monicComplexFiber q₁ d₁ x) (monicComplexFiber q₂ d₂ x) =
        gcdNatDegree
          ((q₁ x).map (algebraMap ℝ ℂ) *
            Polynomial.C ((algebraMap ℝ ℂ ((q₁ x).coeff d₁))⁻¹))
          ((q₂ x).map (algebraMap ℝ ℂ) *
            Polynomial.C ((algebraMap ℝ ℂ ((q₂ x).coeff d₂))⁻¹)) := rfl
    _ = gcdNatDegree
          ((q₁ x).map (algebraMap ℝ ℂ) *
            Polynomial.C ((algebraMap ℝ ℂ ((q₁ x).coeff d₁))⁻¹))
          ((q₂ x).map (algebraMap ℝ ℂ)) :=
      gcdNatDegree_mul_C_right _ _ hq₁scaled hq₂ne _ hc₂
    _ = gcdNatDegree ((q₁ x).map (algebraMap ℝ ℂ))
          ((q₂ x).map (algebraMap ℝ ℂ)) :=
      gcdNatDegree_mul_C_left _ _ hq₁ne hq₂ne _ hc₁

/-- Pairwise equality or disjointness for branches of two positive-degree
    effective reducta. -/
theorem branch_eq_or_ne_of_effective_reducta
    {r : ℕ} {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {B₁ B₂ : Polynomial (MvPolynomial (Fin r) ℝ)}
    {S : Set (Fin r → ℝ)} (hS : IsConnected S)
    (hproj : SignInvariant (collinsProj A) S)
    (hB₁ : B₁ ∈ reductaSet A) (hB₂ : B₂ ∈ reductaSet A)
    (hB₁lc : ∀ a ∈ S, MvPolynomial.eval a B₁.leadingCoeff ≠ 0)
    (hB₂lc : ∀ a ∈ S, MvPolynomial.eval a B₂.leadingCoeff ≠ 0)
    (hd₁ : 0 < B₁.natDegree) (hd₂ : 0 < B₂.natDegree)
    (f g : (Fin r → ℝ) → ℝ)
    (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hfroot : ∀ a ∈ S, Polynomial.eval (f a) (B₁.map (MvPolynomial.eval a)) = 0)
    (hgroot : ∀ a ∈ S, Polynomial.eval (g a) (B₂.map (MvPolynomial.eval a)) = 0) :
    (∀ a ∈ S, f a = g a) ∨ (∀ a ∈ S, f a ≠ g a) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hS.nonempty
  obtain ⟨d₁, m₁, hB₁deg, hd₁', hmapdeg₁, hm₁⟩ :=
    projection_reductum_family_data_of_natDegree_pos hB₁ S hproj hB₁lc ha₀ hd₁
  obtain ⟨d₂, m₂, hB₂deg, hd₂', hmapdeg₂, hm₂⟩ :=
    projection_reductum_family_data_of_natDegree_pos hB₂ S hproj hB₂lc ha₀ hd₂
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS.isPreconnected
  let q₁ : S → Polynomial ℝ := fun a => B₁.map (MvPolynomial.eval a.1)
  let q₂ : S → Polynomial ℝ := fun a => B₂.map (MvPolynomial.eval a.1)
  let p₁ : S → Polynomial ℂ := fun a => monicComplexFiber q₁ d₁ a
  let p₂ : S → Polynomial ℂ := fun a => monicComplexFiber q₂ d₂ a
  have hq₁coeff : ∀ k : ℕ, Continuous (fun a : S => (q₁ a).coeff k) := by
    intro k
    exact (continuous_coeff_map_eval B₁ k).comp continuous_subtype_val
  have hq₂coeff : ∀ k : ℕ, Continuous (fun a : S => (q₂ a).coeff k) := by
    intro k
    exact (continuous_coeff_map_eval B₂ k).comp continuous_subtype_val
  have hq₁lc : ∀ a : S, (q₁ a).coeff d₁ ≠ 0 := by
    intro a
    have hb : B₁.coeff d₁ = B₁.leadingCoeff := by
      rw [← hB₁deg]
      exact Polynomial.coeff_natDegree
    rw [Polynomial.coeff_map, hb]
    exact hB₁lc a.1 a.2
  have hq₂lc : ∀ a : S, (q₂ a).coeff d₂ ≠ 0 := by
    intro a
    have hb : B₂.coeff d₂ = B₂.leadingCoeff := by
      rw [← hB₂deg]
      exact Polynomial.coeff_natDegree
    rw [Polynomial.coeff_map, hb]
    exact hB₂lc a.1 a.2
  have hq₁deg : ∀ a : S, (q₁ a).natDegree = d₁ := by
    intro a
    exact hmapdeg₁ a.1 a.2
  have hq₂deg : ∀ a : S, (q₂ a).natDegree = d₂ := by
    intro a
    exact hmapdeg₂ a.1 a.2
  have hp₁coeff : ∀ k : ℕ, Continuous (fun a : S => (p₁ a).coeff k) := by
    intro k
    exact continuous_monicComplexFiber_coeff q₁ hq₁coeff d₁ hq₁lc k
  have hp₂coeff : ∀ k : ℕ, Continuous (fun a : S => (p₂ a).coeff k) := by
    intro k
    exact continuous_monicComplexFiber_coeff q₂ hq₂coeff d₂ hq₂lc k
  have hp₁monic : ∀ a : S, (p₁ a).Monic :=
    monic_monicComplexFiber q₁ d₁ hq₁deg hq₁lc
  have hp₂monic : ∀ a : S, (p₂ a).Monic :=
    monic_monicComplexFiber q₂ d₂ hq₂deg hq₂lc
  have hp₁roots : ∀ a : S, (p₁ a).roots.toFinset.card = m₁ := by
    intro a
    change (monicComplexFiber q₁ d₁ a).roots.toFinset.card = m₁
    rw [roots_monicComplexFiber q₁ d₁ hq₁lc]
    exact hm₁ a.1 a.2
  have hp₂roots : ∀ a : S, (p₂ a).roots.toFinset.card = m₂ := by
    intro a
    change (monicComplexFiber q₂ d₂ a).roots.toFinset.card = m₂
    rw [roots_monicComplexFiber q₂ d₂ hq₂lc]
    exact hm₂ a.1 a.2
  obtain ⟨gdeg, hgmin, hgcd⟩ :=
    gcd_natDegree_constant_of_signInvariant_collinsProj hB₁ hB₂ hproj hB₁lc hB₂lc ha₀
  have hDmap : ∀ x y : S,
      gcdNatDegree ((q₁ x).map (algebraMap ℝ ℂ))
        ((q₂ x).map (algebraMap ℝ ℂ)) =
      gcdNatDegree ((q₁ y).map (algebraMap ℝ ℂ))
        ((q₂ y).map (algebraMap ℝ ℂ)) := by
    intro x y
    rw [gcdNatDegree_map_real_to_complex, gcdNatDegree_map_real_to_complex]
    exact (hgcd x.1 x.2).trans (hgcd y.1 y.2).symm
  have hD : ∀ x y : S, gcdNatDegree (p₁ x) (p₂ x) = gcdNatDegree (p₁ y) (p₂ y) := by
    intro x y
    dsimp [p₁, p₂]
    rw [gcdNatDegree_monicComplexFiber q₁ q₂ d₁ d₂ x (hq₁lc x) (hq₂lc x),
      gcdNatDegree_monicComplexFiber q₁ q₂ d₁ d₂ y (hq₁lc y) (hq₂lc y)]
    exact hDmap x y
  have hfS : Continuous (fun a : S => f a.1) := by
    rw [continuousOn_iff_continuous_domRestrict] at hf
    exact hf
  have hgS : Continuous (fun a : S => g a.1) := by
    rw [continuousOn_iff_continuous_domRestrict] at hg
    exact hg
  have hfrootC : ∀ a : S, (p₁ a).IsRoot ((f a.1 : ℝ) : ℂ) := by
    intro a
    have hr : (q₁ a).IsRoot (f a.1) := by
      rw [Polynomial.IsRoot.def]
      exact hfroot a.1 a.2
    have hrmap : ((q₁ a).map (algebraMap ℝ ℂ)).IsRoot ((f a.1 : ℝ) : ℂ) :=
      hr.map (algebraMap ℝ ℂ)
    exact Polynomial.root_mul_right_of_isRoot _ hrmap
  have hgrootC : ∀ a : S, (p₂ a).IsRoot ((g a.1 : ℝ) : ℂ) := by
    intro a
    have hr : (q₂ a).IsRoot (g a.1) := by
      rw [Polynomial.IsRoot.def]
      exact hgroot a.1 a.2
    have hrmap : ((q₂ a).map (algebraMap ℝ ℂ)).IsRoot ((g a.1 : ℝ) : ℂ) :=
      hr.map (algebraMap ℝ ℂ)
    exact Polynomial.root_mul_right_of_isRoot _ hrmap
  have hcl := isClopen_rootBranch_eq_of_gcdNatDegree_const
    p₁ p₂ hp₁coeff hp₂coeff d₁ m₁ d₂ m₂ hd₁' hd₂'
    (natDegree_monicComplexFiber q₁ d₁ hq₁deg hq₁lc)
    (natDegree_monicComplexFiber q₂ d₂ hq₂deg hq₂lc)
    hp₁monic hp₂monic hp₁roots hp₂roots hD
    (fun a : S => f a.1) (fun a : S => g a.1) hfS hgS hfrootC hgrootC
  rcases rootBranch_eq_or_ne_of_isClopen hcl with heq | hne
  · left
    intro a ha
    exact heq ⟨a, ha⟩
  · right
    intro a ha
    exact hne ⟨a, ha⟩

/-- Collins' pairwise branch coincidence theorem: two continuous real root
    branches are everywhere equal or everywhere unequal on a connected
    projection-invariant base set. -/
theorem projection_pairwise_disjoint_or_equal {r : ℕ}
    (A : Finset (MvPolynomial (Fin (r + 1)) ℝ))
    (S : Set (Fin r → ℝ)) (hS : IsConnected S)
    (hproj : SignInvariant (collinsProj A) S)
    {P₁ P₂ : MvPolynomial (Fin (r + 1)) ℝ}
    (hP₁ : P₁ ∈ A) (hP₂ : P₂ ∈ A)
    {k l : ℕ} (f : Fin k → (Fin r → ℝ) → ℝ)
    (g : Fin l → (Fin r → ℝ) → ℝ)
    (hf : IsRealRootBranchFamily P₁ S f)
    (hg : IsRealRootBranchFamily P₂ S g) :
    ∀ i j, (∀ a ∈ S, f i a = g j a) ∨ (∀ a ∈ S, f i a ≠ g j a) := by
  classical
  intro i j
  have hL := signInvariant_projL_of_collinsProj hproj
  rcases projection_effective_reductum A P₁ hP₁ S hL with hzero₁ | ⟨k₁, hB₁0, hbridge₁, hB₁lc⟩
  · obtain ⟨a₀, ha₀⟩ := hS.nonempty
    exact (hf.1 a₀ ha₀ (hzero₁ a₀ ha₀)).elim
  · rcases projection_effective_reductum A P₂ hP₂ S hL with hzero₂ | ⟨k₂, hB₂0, hbridge₂, hB₂lc⟩
    · obtain ⟨a₀, ha₀⟩ := hS.nonempty
      exact (hg.1 a₀ ha₀ (hzero₂ a₀ ha₀)).elim
    · let B₁ : Polynomial (MvPolynomial (Fin r) ℝ) :=
        reductum k₁ (finLastEquiv ℝ r P₁)
      let B₂ : Polynomial (MvPolynomial (Fin r) ℝ) :=
        reductum k₂ (finLastEquiv ℝ r P₂)
      have hB₁ : B₁ ∈ reductaSet A := by
        simpa [B₁] using reductum_mem_reductaSet hP₁ hB₁0
      have hB₂ : B₂ ∈ reductaSet A := by
        simpa [B₂] using reductum_mem_reductaSet hP₂ hB₂0
      by_cases hd₁ : B₁.natDegree = 0
      · obtain ⟨a₀, ha₀⟩ := hS.nonempty
        have hc : (B₁.map (MvPolynomial.eval a₀)).coeff 0 ≠ 0 := by
          have hb : B₁.coeff 0 = B₁.leadingCoeff := by
            simp [hd₁, Polynomial.leadingCoeff]
          rw [Polynomial.coeff_map, hb]
          exact hB₁lc a₀ ha₀
        have hdeg0 : (B₁.map (MvPolynomial.eval a₀)).natDegree = 0 := by
          rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (hB₁lc a₀ ha₀), hd₁]
        have heq := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
        have hr := hf.2.2 i a₀ ha₀
        rw [hbridge₁ a₀ ha₀, heq, Polynomial.eval_C] at hr
        exact (hc hr).elim
      · by_cases hd₂ : B₂.natDegree = 0
        · obtain ⟨a₀, ha₀⟩ := hS.nonempty
          have hc : (B₂.map (MvPolynomial.eval a₀)).coeff 0 ≠ 0 := by
            have hb : B₂.coeff 0 = B₂.leadingCoeff := by
              simp [hd₂, Polynomial.leadingCoeff]
            rw [Polynomial.coeff_map, hb]
            exact hB₂lc a₀ ha₀
          have hdeg0 : (B₂.map (MvPolynomial.eval a₀)).natDegree = 0 := by
            rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (hB₂lc a₀ ha₀), hd₂]
          have heq := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
          have hr := hg.2.2 j a₀ ha₀
          rw [hbridge₂ a₀ ha₀, heq, Polynomial.eval_C] at hr
          exact (hc hr).elim
        · exact branch_eq_or_ne_of_effective_reducta hS hproj hB₁ hB₂ hB₁lc hB₂lc
            (Nat.pos_of_ne_zero hd₁) (Nat.pos_of_ne_zero hd₂)
            (f i) (g j) (hf.2.1 i) (hg.2.1 j)
            (fun a ha => by rw [← hbridge₁ a ha]; exact hf.2.2 i a ha)
            (fun a ha => by rw [← hbridge₂ a ha]; exact hg.2.2 j a ha)

end CollinsCAD
