import Mathlib
import Analysis.LocalRoots

namespace CollinsCAD

open Polynomial Filter

/-!
## Global ordered real root functions

For a continuous family of monic real-coefficient polynomials of constant degree
and constant distinct-root count over a preconnected space, the real roots can be
ordered globally into continuous functions. This is the topological core of
Collins' Theorem 1.
-/

/-- Global continuous ordered real root functions for a monic real family. -/
theorem ordered_real_root_functions_of_family
    {X : Type*} [PseudoMetricSpace X] [PreconnectedSpace X] [Nonempty X]
    (p : X → Polynomial ℂ)
    (hcoeff : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (d m : ℕ) (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree = d)
    (hmonic : ∀ x, (p x).Monic)
    (hm : ∀ x, (p x).roots.toFinset.card = m)
    (hreal : ∀ x k, ((p x).coeff k).im = 0) :
    ∃ (k : ℕ) (f : Fin k → X → ℝ),
      (∀ i, Continuous (f i)) ∧
      (∀ i x, (p x).IsRoot ((f i x : ℝ) : ℂ) ∧ ((f i x : ℝ) : ℂ).im = 0) ∧
      (∀ (x : X) (z : ℂ), (p x).IsRoot z → z.im = 0 → ∃ i, (f i x : ℂ) = z) ∧
      (∀ (i j : Fin k) x, i < j → f i x < f j x) := by
  classical
  let T : X → Finset ℂ := fun x => (p x).roots.toFinset.filter (fun z => z.im = 0)
  let S : X → Finset ℝ := fun x => (T x).image Complex.re
  have hcardTS : ∀ x, (S x).card = (T x).card := by
    intro x
    dsimp [S]
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    apply Complex.ext
    · exact hab
    · rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2]
  obtain ⟨x0base⟩ := ‹Nonempty X›
  let k : ℕ := (S x0base).card
  have hkS : ∀ x, (S x).card = k := by
    intro x
    have hT : (T x).card = (T x0base).card := by
      dsimp [T]
      exact real_root_count_constant_on_preconnected p hcoeff d m hd hdeg hmonic hm hreal x x0base
    dsimp [k]
    rw [hcardTS x, hcardTS x0base, hT]
  let f : Fin k → X → ℝ := fun i x => ((S x).orderEmbOfFin (hkS x)) i
  have hfroot : ∀ i x, (p x).IsRoot ((f i x : ℝ) : ℂ) ∧ ((f i x : ℝ) : ℂ).im = 0 := by
    intro i x
    have hmem : ((S x).orderEmbOfFin (hkS x)) i ∈ S x :=
      Finset.orderEmbOfFin_mem (S x) (hkS x) i
    rcases Finset.mem_image.mp hmem with ⟨z, hzT, hzre⟩
    have hzrootmem : z ∈ (p x).roots.toFinset := (Finset.mem_filter.mp hzT).1
    have hzim : z.im = 0 := (Finset.mem_filter.mp hzT).2
    have hzre' : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [hzim]
    dsimp [f]
    rw [← hzre]
    rw [hzre']
    constructor
    · exact Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hzrootmem)
    · simp
  have hfexhaust : ∀ (x : X) (z : ℂ), (p x).IsRoot z → z.im = 0 →
      ∃ i, (f i x : ℂ) = z := by
    intro x z hzroot hzim
    have hzT : z ∈ T x := by
      exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots (hmonic x).ne_zero).mpr hzroot), hzim⟩
    have hzS : z.re ∈ S x := Finset.mem_image.mpr ⟨z, hzT, rfl⟩
    rcases ((S x).orderIsoOfFin (hkS x)).surjective ⟨z.re, hzS⟩ with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hpair := hi
    have hval : ((S x).orderEmbOfFin (hkS x)) i = z.re := by
      simpa using congrArg Subtype.val hpair
    have hzre' : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [hzim]
    dsimp [f]
    rw [hval]
    exact hzre'
  have hfmono : ∀ (i j : Fin k) x, i < j → f i x < f j x := by
    intro i j x hij
    exact (S x).orderEmbOfFin (hkS x) |>.strictMono hij
  have hfcont : ∀ i, Continuous (f i) := by
    intro i
    rw [continuous_iff_continuousAt]
    intro x0'
    obtain ⟨U, ε, g, hUopen, hx0U, hεpos, hcont, hrootprop, hrealpres,
      hcover, hsep4, huniq⟩ :=
      local_real_root_functions p hcoeff d m hd hdeg hmonic hm hreal x0'
    have hchoose : ∀ r : ℝ, r ∈ S x0' →
        ∃ z : ℂ, z ∈ T x0' ∧ z.re = r := by
      intro r hr
      exact Finset.mem_image.mp hr
    let zbranch : ℝ → ℂ := fun r =>
      if hr : r ∈ S x0' then Classical.choose (hchoose r hr) else 0
    have hzbranch_re : ∀ r (hr : r ∈ S x0'), (zbranch r).re = r := by
      intro r hr
      dsimp [zbranch]
      rw [dite_eq_left hr]
      exact (Classical.choose_spec (hchoose r hr)).2
    have hzbranch_T : ∀ r (hr : r ∈ S x0'), zbranch r ∈ T x0' := by
      intro r hr
      dsimp [zbranch]
      rw [dite_eq_left hr]
      exact (Classical.choose_spec (hchoose r hr)).1
    have hzbranch_roots : ∀ r (hr : r ∈ S x0'), zbranch r ∈ (p x0').roots.toFinset := by
      intro r hr
      exact (Finset.mem_filter.mp (hzbranch_T r hr)).1
    have hzbranch_im : ∀ r (hr : r ∈ S x0'), (zbranch r).im = 0 := by
      intro r hr
      exact (Finset.mem_filter.mp (hzbranch_T r hr)).2
    let oc : ℝ := ((S x0').orderEmbOfFin (hkS x0')) i
    have hoc : oc ∈ S x0' := Finset.orderEmbOfFin_mem (S x0') (hkS x0') i
    have hb0 : ContinuousAt (g (zbranch oc)) x0' :=
      (hcont (zbranch oc) (hzbranch_roots oc hoc)).continuousAt
        (hUopen.mem_nhds hx0U)
    have hbranch : ContinuousAt (fun y => (g (zbranch oc) y).re) x0' := by
      exact (Complex.continuous_re.tendsto (g (zbranch oc) x0')).comp hb0
    apply hbranch.congr_of_eventuallyEq
    filter_upwards [hUopen.mem_nhds hx0U] with y hy
    let hfun : Fin k → ℝ := fun j =>
      (g (zbranch (((S x0').orderEmbOfFin (hkS x0')) j)) y).re
    have hmem : ∀ j, hfun j ∈ S y := by
      intro j
      let r := ((S x0').orderEmbOfFin (hkS x0')) j
      have hr : r ∈ S x0' := Finset.orderEmbOfFin_mem (S x0') (hkS x0') j
      have hp := hrootprop (zbranch r) (hzbranch_roots r hr) y hy
      have hrew : (g (zbranch r) y).im = 0 :=
        hrealpres (zbranch r) (hzbranch_roots r hr) (hzbranch_im r hr) y hy
      exact Finset.mem_image.mpr ⟨g (zbranch r) y,
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots (hmonic y).ne_zero).mpr hp.1), hrew⟩, rfl⟩
    have hstrict : StrictMono hfun := by
      intro j1 j2 hj
      let r1 := ((S x0').orderEmbOfFin (hkS x0')) j1
      let r2 := ((S x0').orderEmbOfFin (hkS x0')) j2
      have hr1 : r1 ∈ S x0' := Finset.orderEmbOfFin_mem (S x0') (hkS x0') j1
      have hr2 : r2 ∈ S x0' := Finset.orderEmbOfFin_mem (S x0') (hkS x0') j2
      have hr12 : r1 < r2 := (S x0').orderEmbOfFin (hkS x0') |>.strictMono hj
      have hz1re : (zbranch r1).re = r1 := hzbranch_re r1 hr1
      have hz2re : (zbranch r2).re = r2 := hzbranch_re r2 hr2
      have hd1 := (hrootprop (zbranch r1) (hzbranch_roots r1 hr1) y hy).2
      have hd2 := (hrootprop (zbranch r2) (hzbranch_roots r2 hr2) y hy).2
      have hne : zbranch r1 ≠ zbranch r2 := by
        intro heq
        have : r1 = r2 := by rw [← hz1re, ← hz2re, heq]
        exact (ne_of_lt hr12) this
      have hs' := hsep4 (zbranch r1) (hzbranch_roots r1 hr1)
        (zbranch r2) (hzbranch_roots r2 hr2) hne
      have hrew1 : (g (zbranch r1) y).im = 0 :=
        hrealpres (zbranch r1) (hzbranch_roots r1 hr1) (hzbranch_im r1 hr1) y hy
      have hrew2 : (g (zbranch r2) y).im = 0 :=
        hrealpres (zbranch r2) (hzbranch_roots r2 hr2) (hzbranch_im r2 hr2) y hy
      have hd1r : dist (g (zbranch r1) y).re (zbranch r1).re < ε := by
        rw [← Complex.dist_of_im_eq (by rw [hrew1, hzbranch_im r1 hr1])]
        exact hd1
      have hd2r : dist (g (zbranch r2) y).re (zbranch r2).re < ε := by
        rw [← Complex.dist_of_im_eq (by rw [hrew2, hzbranch_im r2 hr2])]
        exact hd2
      have hsr : dist (zbranch r1).re (zbranch r2).re =
          (zbranch r2).re - (zbranch r1).re := by
        rw [Real.dist_eq, abs_of_nonpos]
        · rw [hz1re, hz2re]
          linarith
        · rw [hz1re, hz2re]
          linarith
      rw [Complex.dist_of_im_eq (by rw [hzbranch_im r1 hr1, hzbranch_im r2 hr2]), hsr] at hs'
      rw [Real.dist_eq] at hd1r hd2r
      rw [abs_sub_lt_iff] at hd1r hd2r
      dsimp [hfun]
      linarith
    have huniqemb := Finset.orderEmbOfFin_unique (hkS y) hmem hstrict
    have hpoint : ((S y).orderEmbOfFin (hkS y)) i = hfun i := by
      rw [← huniqemb]
    dsimp [f]
    rw [hpoint]
  exact ⟨k, f, hfcont, hfroot, hfexhaust, hfmono⟩

/-- Global ordered real root functions with constant multiplicities. -/
theorem ordered_real_root_functions_with_multiplicity
    {X : Type*} [PseudoMetricSpace X] [PreconnectedSpace X] [Nonempty X]
    (p : X → Polynomial ℂ)
    (hcoeff : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (d m : ℕ) (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree = d)
    (hmonic : ∀ x, (p x).Monic)
    (hm : ∀ x, (p x).roots.toFinset.card = m)
    (hreal : ∀ x k, ((p x).coeff k).im = 0) :
    ∃ (k : ℕ) (f : Fin k → X → ℝ) (e : Fin k → ℕ),
      (∀ i, Continuous (f i)) ∧
      (∀ i x, 0 < e i ∧ (p x).IsRoot ((f i x : ℝ) : ℂ) ∧
        Polynomial.rootMultiplicity ((f i x : ℝ) : ℂ) (p x) = e i) ∧
      (∀ (x : X) (z : ℂ), (p x).IsRoot z → z.im = 0 → ∃ i, (f i x : ℂ) = z) ∧
      (∀ (i j : Fin k) x, i < j → f i x < f j x) := by
  classical
  obtain ⟨k, f, hfcont, hfroot, hfexhaust, hfmono⟩ :=
    ordered_real_root_functions_of_family p hcoeff d m hd hdeg hmonic hm hreal
  obtain ⟨x0base⟩ := ‹Nonempty X›
  let e : Fin k → ℕ := fun i => Polynomial.rootMultiplicity ((f i x0base : ℝ) : ℂ) (p x0base)
  have hepos : ∀ i, 0 < e i := by
    intro i
    dsimp [e]
    exact (Polynomial.rootMultiplicity_pos (hmonic x0base).ne_zero).mpr (hfroot i x0base).1
  have heq : ∀ i x, Polynomial.rootMultiplicity ((f i x : ℝ) : ℂ) (p x) = e i := by
    intro i x
    let mu : X → ℕ := fun y => Polynomial.rootMultiplicity ((f i y : ℝ) : ℂ) (p y)
    have hloc : IsLocallyConstant mu := by
      rw [IsLocallyConstant.iff_exists_open]
      intro x0
      obtain ⟨U, ε, _g, hUopen, hx0U, hεpos, _hcont, _hrootprop,
        huniq, _hcover, hsep4⟩ :=
        local_continuous_root_functions p hcoeff d m hd hdeg hmonic hm x0
      let z0 : ℂ := ((f i x0 : ℝ) : ℂ)
      have hz0root : (p x0).IsRoot z0 := (hfroot i x0).1
      have hz0roots : z0 ∈ (p x0).roots.toFinset :=
        Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots (hmonic x0).ne_zero).mpr hz0root)
      have hsepz : ∀ β ∈ (p x0).roots.toFinset, β ≠ z0 →
          2 * ε ≤ dist β z0 := by
        intro β hβ hβz
        have hs := hsep4 z0 hz0roots β hβ (Ne.symm hβz)
        rw [dist_comm]
        linarith
      have huniqz : ∀ y ∈ U, ∃! w : ℂ,
          (p y).IsRoot w ∧ dist w z0 < ε := by
        intro y hy
        exact huniq z0 hz0roots y hy
      have hficont : Continuous (fun y => ((f i y : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp (hfcont i)
      obtain ⟨V, hVopen, hx0V, _hVU, hmult⟩ :=
        rootMultiplicity_locally_constant_of_continuous_root_in_ball
          p hcoeff d hd hdeg hmonic x0 z0 ε hεpos hz0root hsepz
          U hUopen hx0U (fun y => ((f i y : ℝ) : ℂ))
          hficont.continuousOn (fun y _ => (hfroot i y).1) rfl huniqz
      refine ⟨V, hVopen, hx0V, ?_⟩
      intro y hy
      simpa [mu, z0] using hmult y hy
    change mu x = mu x0base
    exact hloc.apply_eq_of_preconnectedSpace x x0base
  exact ⟨k, f, e, hfcont, fun i x => ⟨hepos i, (hfroot i x).1, heq i x⟩, hfexhaust, hfmono⟩


/-- Collins' Theorem 1 (real-root form) for a continuous monic family: the real
    roots of a monic real-coefficient polynomial family with constant degree and
    constant distinct-root count over a preconnected parameter space are
    delineated by a finite ordered family of continuous functions with constant
    multiplicities. -/
theorem delineability_theorem_1_real
    {X : Type*} [PseudoMetricSpace X] [PreconnectedSpace X] [Nonempty X]
    (p : X → Polynomial ℂ)
    (hcoeff : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (d m : ℕ) (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree = d)
    (hmonic : ∀ x, (p x).Monic)
    (hm : ∀ x, (p x).roots.toFinset.card = m)
    (hreal : ∀ x k, ((p x).coeff k).im = 0) :
    ∃ (k : ℕ) (f : Fin k → X → ℝ) (e : Fin k → ℕ),
      (∀ i, Continuous (f i)) ∧
      (∀ i x, 0 < e i ∧ (p x).IsRoot ((f i x : ℝ) : ℂ) ∧
        Polynomial.rootMultiplicity ((f i x : ℝ) : ℂ) (p x) = e i) ∧
      (∀ (x : X) (z : ℂ), (p x).IsRoot z → z.im = 0 → ∃ i, (f i x : ℂ) = z) ∧
      (∀ (i j : Fin k) x, i < j → f i x < f j x) :=
  ordered_real_root_functions_with_multiplicity p hcoeff d m hd hdeg hmonic hm hreal

end CollinsCAD
