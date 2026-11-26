import Mathlib
import Analysis.RootContinuity

namespace CollinsCAD

open Polynomial Filter

/-!
## Local root functions

A root that is isolated in a small disc can be followed continuously along any
continuous family of polynomials. This is the local input needed to glue the
ordered root functions of Collins' Theorem 1.
-/

/-- A finite set of complex numbers admits a positive radius such that the
    discs of that radius around distinct points are pairwise disjoint. -/
theorem exists_separation_radius (s : Finset ℂ) :
    ∃ ε > 0, ∀ z ∈ s, ∀ w ∈ s, z ≠ w → 2 * ε ≤ dist z w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · exact ⟨1, zero_lt_one, by simp⟩
  · intro a t hat ih
    rcases ih with ⟨ε, hεpos, hsep⟩
    by_cases ht : t.Nonempty
    · let D : ℝ := (t.image (fun w => dist a w)).min' (by
        simpa using ht.image (fun w => dist a w))
      have hDmem : D ∈ t.image (fun w => dist a w) := Finset.min'_mem _ _
      rcases Finset.mem_image.mp hDmem with ⟨w0, hw0t, hw0eq⟩
      have hDpos : 0 < D := by
        rw [← hw0eq]
        apply dist_pos.mpr
        intro h
        apply hat
        simpa [h] using hw0t
      refine ⟨min ε (D / 2), lt_min hεpos (by linarith), ?_⟩
      intro z hz w hw hzw
      simp at hz hw
      rcases hz with hza | hzt
      · subst z
        rcases hw with hwa | hwt
        · subst w
          contradiction
        · have hDle : D ≤ dist a w := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨w, hwt, rfl⟩)
          have hle := min_le_right ε (D / 2)
          linarith
      · rcases hw with hwa | hwt
        · subst w
          have hDle : D ≤ dist a z := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨z, hzt, rfl⟩)
          have hle := min_le_right ε (D / 2)
          rw [dist_comm]
          linarith
        · have hle := min_le_left ε (D / 2)
          have hs := hsep z hzt w hwt hzw
          linarith
    · refine ⟨ε, hεpos, ?_⟩
      intro z hz w hw hzw
      rw [Finset.mem_insert] at hz hw
      rcases hz with hza | hzt
      · subst z
        rcases hw with hwa | hwt
        · subst w
          contradiction
        · exact False.elim (ht ⟨w, hwt⟩)
      · exact False.elim (ht ⟨z, hzt⟩)

/-- If two monic polynomials have equally many distinct roots and the exact
    count of roots in each separating disc is preserved, then each disc contains
    a unique root of the second polynomial. -/
theorem unique_root_in_ball_of_count
    (P Q : Polynomial ℂ) (ε : ℝ) (_hε : 0 < ε)
    (hsep : ∀ z ∈ P.roots.toFinset, ∀ w ∈ P.roots.toFinset, z ≠ w →
      2 * ε ≤ dist z w)
    (hcount : ∀ z ∈ P.roots.toFinset,
      (Q.roots.filter (fun u => dist u z < ε)).card = P.roots.count z)
    (hcard : Q.roots.toFinset.card = P.roots.toFinset.card) :
    (∀ z ∈ P.roots.toFinset, ∃! w : ℂ, w ∈ Q.roots.toFinset ∧ dist w z < ε) ∧
    (∀ w ∈ Q.roots.toFinset, ∃ z ∈ P.roots.toFinset, dist w z < ε) := by
  classical
  let s := P.roots.toFinset
  let T : ℂ → Finset ℂ := fun z => (Q.roots.filter (fun u => dist u z < ε)).toFinset
  have hTpos : ∀ z ∈ s, 0 < (T z).card := by
    intro z hz
    have hzmem : z ∈ P.roots := Multiset.mem_toFinset.mp (by simpa [s] using hz)
    have hc := hcount z (by simpa [s] using hz)
    have hpos : 0 < P.roots.count z := Multiset.count_pos.mpr hzmem
    dsimp [T]
    have hmcard : 0 < (Q.roots.filter (fun u => dist u z < ε)).card := by
      rw [hc]
      exact hpos
    have hmne : (Q.roots.filter (fun u => dist u z < ε)) ≠ 0 :=
      Multiset.card_pos.mp hmcard
    exact Finset.card_pos.mpr (Multiset.toFinset_nonempty.mpr hmne)
  have hdisj : (↑s : Set ℂ).PairwiseDisjoint T := by
    intro z hz w hw hzw
    change Disjoint (T z) (T w)
    rw [Finset.disjoint_left]
    intro v hvz hvw
    have hvzmem : v ∈ Q.roots.filter (fun u => dist u z < ε) :=
      Multiset.mem_toFinset.mp (by simpa [T] using hvz)
    have hvwmem : v ∈ Q.roots.filter (fun u => dist u w < ε) :=
      Multiset.mem_toFinset.mp (by simpa [T] using hvw)
    have hdz : dist v z < ε := (Multiset.mem_filter.mp hvzmem).2
    have hdw : dist v w < ε := (Multiset.mem_filter.mp hvwmem).2
    have htri : dist z w ≤ dist z v + dist v w := dist_triangle _ _ _
    rw [dist_comm z v] at htri
    have hs := hsep z (by simpa [s] using hz) w (by simpa [s] using hw) hzw
    linarith
  have hTcard : (s.biUnion T).card = ∑ z ∈ s, (T z).card := Finset.card_biUnion hdisj
  have hTsubset : s.biUnion T ⊆ Q.roots.toFinset := by
    intro v hv
    simp only [Finset.mem_biUnion] at hv
    rcases hv with ⟨z, hzs, hvz⟩
    have hvzmem : v ∈ Q.roots.filter (fun u => dist u z < ε) :=
      Multiset.mem_toFinset.mp (by simpa [T] using hvz)
    exact Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp hvzmem).1
  have hsum_le : (∑ z ∈ s, (T z).card) ≤ s.card := by
    rw [← hTcard]
    calc
      (s.biUnion T).card ≤ Q.roots.toFinset.card := Finset.card_le_card hTsubset
      _ = s.card := by simpa [s] using hcard
  have hsum_ge : s.card ≤ ∑ z ∈ s, (T z).card := by
    calc
      s.card = ∑ z ∈ s, 1 := by simp
      _ ≤ ∑ z ∈ s, (T z).card := Finset.sum_le_sum
        (fun z hz => Nat.succ_le_of_lt (hTpos z hz))
  have hsum_eq : (∑ z ∈ s, (T z).card) = s.card := le_antisymm hsum_le hsum_ge
  have hbi_card : (s.biUnion T).card = Q.roots.toFinset.card := by
    rw [hTcard, hsum_eq, hcard]
  have hbi_eq : s.biUnion T = Q.roots.toFinset := by
    exact (Finset.subset_iff_eq_of_card_le (by rw [hbi_card])).mp hTsubset
  have hcover : ∀ w ∈ Q.roots.toFinset, ∃ z ∈ s, dist w z < ε := by
    intro w hw
    have hwbi : w ∈ s.biUnion T := by simpa [hbi_eq] using hw
    simp only [Finset.mem_biUnion] at hwbi
    rcases hwbi with ⟨z, hzs, hwT⟩
    refine ⟨z, hzs, ?_⟩
    have hwfilter : w ∈ Q.roots.filter (fun u => dist u z < ε) :=
      Multiset.mem_toFinset.mp (by simpa [T] using hwT)
    exact (Multiset.mem_filter.mp hwfilter).2
  constructor
  · intro z hz
    have hTzcard : (T z).card = 1 := by
      by_contra hne
      have hgt : 1 < (T z).card :=
        lt_of_le_of_ne (Nat.succ_le_of_lt (hTpos z hz)) (fun h => hne h.symm)
      have hsum_gt : s.card < ∑ y ∈ s, (T y).card := by
        calc
          s.card = ∑ y ∈ s, 1 := by simp
          _ < ∑ y ∈ s, (T y).card := Finset.sum_lt_sum
            (fun y hy => Nat.succ_le_of_lt (hTpos y hy)) ⟨z, hz, hgt⟩
      rw [hsum_eq] at hsum_gt
      exact (lt_irrefl _ hsum_gt)
    rcases Finset.card_eq_one.mp hTzcard with ⟨w, hwT⟩
    have hwmemT : w ∈ T z := by simp [hwT]
    have hwfilter : w ∈ Q.roots.filter (fun u => dist u z < ε) :=
      Multiset.mem_toFinset.mp (by simpa [T] using hwmemT)
    refine ⟨w, ?_, ?_⟩
    · exact ⟨Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp hwfilter).1,
        (Multiset.mem_filter.mp hwfilter).2⟩
    · intro v hv
      have hvfilter : v ∈ Q.roots.filter (fun u => dist u z < ε) :=
        Multiset.mem_filter.mpr ⟨Multiset.mem_toFinset.mp hv.1, hv.2⟩
      have hvT : v ∈ T z :=
        Multiset.mem_toFinset.mpr (by simpa [T] using hvfilter)
      simpa [hwT] using hvT
  · simpa [s] using hcover

/-- Local uniqueness of roots: around a base point $x_0$, every disc around a
    distinct root of $p(x_0)$ contains a unique root of $p(x)$, provided the
    family is monic of constant degree and has constantly many distinct roots. -/
theorem locally_unique_roots_of_monic_family
    {X : Type*} [PseudoMetricSpace X]
    (p : X → Polynomial ℂ)
    (hcoeff : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (d m : ℕ) (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree = d)
    (hmonic : ∀ x, (p x).Monic)
    (hm : ∀ x, (p x).roots.toFinset.card = m)
    (x0 : X) :
    ∃ (U : Set X) (ε : ℝ), IsOpen U ∧ x0 ∈ U ∧ 0 < ε ∧
      (∀ z ∈ (p x0).roots.toFinset, ∀ w ∈ (p x0).roots.toFinset,
        z ≠ w → 3 * ε < dist z w) ∧
      (∀ z ∈ (p x0).roots.toFinset, ∀ x ∈ U,
        ∃! w : ℂ, (p x).IsRoot w ∧ dist w z < ε) ∧
      (∀ x ∈ U, ∀ w ∈ (p x).roots.toFinset,
        ∃ z ∈ (p x0).roots.toFinset, dist w z < ε) := by
  classical
  let s := (p x0).roots.toFinset
  have hcard0 : (p x0).roots.card = d := by
    have hs := Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits (p x0))
    simpa [hdeg x0] using hs.symm
  have hsne : s.Nonempty := by
    dsimp [s]
    exact Multiset.toFinset_nonempty.mpr (Multiset.card_pos.mp (by rw [hcard0]; exact hd))
  obtain ⟨ε0, hε0pos, hsep0⟩ := exists_separation_radius s
  let ε : ℝ := ε0 / 2
  have hεpos : 0 < ε := by dsimp [ε]; linarith
  have hsep : ∀ z ∈ s, ∀ w ∈ s, z ≠ w → 2 * ε ≤ dist z w := by
    intro z hz w hw hzw
    have hs := hsep0 z hz w hw hzw
    dsimp [ε]
    linarith
  have hsep4 : ∀ z ∈ s, ∀ w ∈ s, z ≠ w → 3 * ε < dist z w := by
    intro z hz w hw hzw
    have hs := hsep0 z hz w hw hzw
    dsimp [ε]
    linarith
  have hone : ∀ z ∈ s, ∃ δ > 0, ∀ Q : Polynomial ℂ, Q.Monic → Q.natDegree = d →
      (∀ k ≤ d, ‖Q.coeff k - (p x0).coeff k‖ < δ) →
      (Q.roots.filter (fun u => dist u z < ε)).card = (p x0).roots.count z := by
    intro z hz
    have hzroot : (p x0).IsRoot z :=
      Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp (by simpa [s] using hz))
    have hsepz : ∀ β ∈ (p x0).roots.toFinset, β ≠ z → 2 * ε ≤ dist β z := by
      intro β hβ hβz
      have hs' := hsep β (by simpa [s] using hβ) z (by simpa [s] using hz) hβz
      simpa [dist_comm] using hs'
    simpa [hdeg x0] using roots_count_in_ball_eq_of_coeff_close (p x0) (hmonic x0)
      (by simpa [hdeg x0] using hd) z hzroot ε hεpos hsepz
  let δfun : ℂ → ℝ := fun z => if hz : z ∈ s then Classical.choose (hone z hz) else 1
  have hδfunpos : ∀ z ∈ s, 0 < δfun z := by
    intro z hz
    dsimp [δfun]
    rw [dite_eq_left hz]
    exact (Classical.choose_spec (hone z hz)).1
  let δ : ℝ := (s.image δfun).min' (by simpa using hsne.image δfun)
  have hδpos : 0 < δ := by
    have hmem : δ ∈ s.image δfun := Finset.min'_mem _ _
    rcases Finset.mem_image.mp hmem with ⟨z, hzs, hzeq⟩
    rw [← hzeq]
    exact hδfunpos z hzs
  have hδle : ∀ z ∈ s, δ ≤ δfun z := by
    intro z hz
    dsimp [δ]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  let U : Set X := {x | ∀ k : Fin (d + 1),
    ‖(p x).coeff (k : ℕ) - (p x0).coeff (k : ℕ)‖ < δ}
  have hUopen : IsOpen U := by
    dsimp [U]
    have h : IsOpen (⋂ k : Fin (d + 1),
        {x : X | ‖(p x).coeff (k : ℕ) - (p x0).coeff (k : ℕ)‖ < δ}) := by
      apply isOpen_iInter_of_finite
      intro k
      exact isOpen_lt ((hcoeff (k : ℕ)).sub continuous_const).norm continuous_const
    have hset : (⋂ k : Fin (d + 1),
        {x : X | ‖(p x).coeff (k : ℕ) - (p x0).coeff (k : ℕ)‖ < δ}) =
        {x : X | ∀ k : Fin (d + 1),
          ‖(p x).coeff (k : ℕ) - (p x0).coeff (k : ℕ)‖ < δ} := by
      ext x
      simp
    rw [← hset]
    exact h
  have hx0U : x0 ∈ U := by
    intro k
    simp
    exact hδpos
  have hcount_all : ∀ x ∈ U, ∀ z' ∈ (p x0).roots.toFinset,
      ((p x).roots.filter (fun u => dist u z' < ε)).card =
        (p x0).roots.count z' := by
    intro x hxU z' hz'
    have hclose : ∀ k ≤ d, ‖(p x).coeff k - (p x0).coeff k‖ < δ := by
      intro k hk
      exact hxU ⟨k, by omega⟩
    have hδle_choose : δ ≤ Classical.choose (hone z' hz') := by
      have hle := hδle z' hz'
      dsimp [δfun] at hle
      rw [dite_eq_left hz'] at hle
      exact hle
    apply (Classical.choose_spec (hone z' hz')).2 (p x) (hmonic x) (by simp [hdeg x])
    intro k hk
    exact lt_of_lt_of_le (hclose k hk) hδle_choose
  have hcard : ∀ x, (p x).roots.toFinset.card = (p x0).roots.toFinset.card := by
    intro x
    rw [hm x, hm x0]
  refine ⟨U, ε, hUopen, hx0U, hεpos, ?_, ?_, ?_⟩
  · simpa [s] using hsep4
  · intro z hz x hxU
    have huniq := (unique_root_in_ball_of_count (p x0) (p x) ε hεpos hsep
      (hcount_all x hxU) (hcard x)).1 z hz
    rcases huniq with ⟨w, hw, huniqw⟩
    refine ⟨w, ?_, ?_⟩
    · exact ⟨Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hw.1), hw.2⟩
    · intro v hv
      apply huniqw v
      refine ⟨Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots (hmonic x).ne_zero).mpr hv.1), hv.2⟩
  · intro x hxU w hw
    simpa [s] using (unique_root_in_ball_of_count (p x0) (p x) ε hεpos hsep
      (hcount_all x hxU) (hcard x)).2 w hw
/-- Evaluation of a polynomial of degree at most $d$ as a sum over
    $\mathrm{Fin}(d+1)$. -/
theorem eval_eq_sum_fin {P : Polynomial ℂ} {d : ℕ} (hd : P.natDegree ≤ d) (z : ℂ) :
    Polynomial.eval z P = ∑ k : Fin (d + 1), P.coeff (k : ℕ) * z ^ (k : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (p := P) (n := d + 1) (by omega) z]
  rw [← Fin.sum_univ_eq_sum_range (fun k => P.coeff k * z ^ k) (d + 1)]

/-- Evaluation of a degree-$d$ polynomial from its coefficient vector and a
    point. -/
def evalFin (d : ℕ) (q : (Fin (d + 1) → ℂ) × ℂ) : ℂ :=
  ∑ k : Fin (d + 1), q.1 k * q.2 ^ (k : ℕ)

/-- Joint continuity of evaluation in the coefficient vector and the point. -/
theorem continuous_evalFin (d : ℕ) : Continuous (evalFin d) := by
  unfold evalFin
  fun_prop

/-- A root selected continuously from an isolated disc: if for every $x$ the
    polynomial $p(x)$ has a unique root in $B(\alpha,\varepsilon)$, and every
    root of $p(x)$ within $2\varepsilon$ of $\alpha$ is that selected root, then
    the selected root depends continuously on $x$. -/
theorem continuous_unique_root_in_ball
    {X : Type*} [PseudoMetricSpace X]
    (p : X → Polynomial ℂ)
    (hcoeff : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (d : ℕ) (hdeg : ∀ x, (p x).natDegree = d)
    (α : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hsel : ∀ x, ∃! z : ℂ, (p x).IsRoot z ∧ dist z α < ε)
    (hisolate : ∀ x (z : ℂ), (p x).IsRoot z → dist z α < 2 * ε →
      z = Classical.choose (hsel x)) :
    Continuous (fun x => Classical.choose (hsel x)) := by
  let zsel : X → ℂ := fun x => Classical.choose (hsel x)
  have hzspec : ∀ x, (p x).IsRoot (zsel x) ∧ dist (zsel x) α < ε := by
    intro x
    exact (Classical.choose_spec (hsel x)).1
  rw [continuous_iff_seqContinuous]
  intro u x hux
  change Tendsto (fun n => zsel (u n)) atTop (nhds (zsel x))
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have huxns : Tendsto (u ∘ ns) atTop (nhds x) := hux.comp hns
  have hbound_norm : ∀ n, ‖zsel (u (ns n))‖ ≤ ‖α‖ + ε := by
    intro n
    have hdist := (hzspec (u (ns n))).2
    have htri : ‖zsel (u (ns n))‖ ≤ ‖zsel (u (ns n)) - α‖ + ‖α‖ := by
      simpa [dist_eq_norm] using dist_triangle (zsel (u (ns n))) α 0
    rw [dist_eq_norm] at hdist
    linarith
  let K : Set ℂ := Metric.closedBall (0 : ℂ) (‖α‖ + ε)
  have hKcpt : IsCompact K := ProperSpace.isCompact_closedBall 0 (‖α‖ + ε)
  have hmem : ∀ n, zsel (u (ns n)) ∈ K := by
    intro n
    simpa [K, Metric.mem_closedBall, dist_eq_norm] using hbound_norm n
  rcases hKcpt.tendsto_subseq hmem with ⟨w, hwK, ms, hmsmono, hmstend⟩
  refine ⟨ms, ?_⟩
  have hcoeff_tend : ∀ k : Fin (d + 1),
      Tendsto (fun n => (p (u (ns (ms n)))).coeff (k : ℕ)) atTop
        (nhds ((p x).coeff (k : ℕ))) := by
    intro k
    exact ((hcoeff (k : ℕ)).tendsto x).comp (huxns.comp hmsmono.tendsto_atTop)
  have hvec_tend : Tendsto
      (fun n => fun k : Fin (d + 1) => (p (u (ns (ms n)))).coeff (k : ℕ)) atTop
      (nhds (fun k : Fin (d + 1) => (p x).coeff (k : ℕ))) := by
    rw [tendsto_pi_nhds]
    exact hcoeff_tend
  have hpair : Tendsto
      (fun n => ((fun k : Fin (d + 1) => (p (u (ns (ms n)))).coeff (k : ℕ)),
        zsel (u (ns (ms n))))) atTop
      (nhds ((fun k : Fin (d + 1) => (p x).coeff (k : ℕ)), w)) :=
    hvec_tend.prodMk_nhds hmstend
  have heval_tend : Tendsto
      (fun n => evalFin d
        ((fun k : Fin (d + 1) => (p (u (ns (ms n)))).coeff (k : ℕ)),
          zsel (u (ns (ms n))))) atTop
      (nhds (evalFin d ((fun k : Fin (d + 1) => (p x).coeff (k : ℕ)), w))) :=
    ((continuous_evalFin d).tendsto _).comp hpair
  have hzero : ∀ n, evalFin d
        ((fun k : Fin (d + 1) => (p (u (ns (ms n)))).coeff (k : ℕ)),
          zsel (u (ns (ms n)))) = 0 := by
    intro n
    rw [evalFin]
    rw [← eval_eq_sum_fin (d := d) (by simp [hdeg]) (zsel (u (ns (ms n))))]
    exact (hzspec (u (ns (ms n)))).1
  have heval_w : evalFin d ((fun k : Fin (d + 1) => (p x).coeff (k : ℕ)), w) = 0 :=
    tendsto_nhds_unique_of_eventuallyEq heval_tend tendsto_const_nhds
      (Eventually.of_forall hzero)
  have hwroot : (p x).IsRoot w := by
    change Polynomial.eval w (p x) = 0
    rw [eval_eq_sum_fin (d := d) (by simp [hdeg]) w]
    simpa [evalFin] using heval_w
  have hwdist : dist w α ≤ ε := by
    have hclosed : IsClosed (Metric.closedBall α ε) := Metric.isClosed_closedBall
    have hev : ∀ᶠ n in atTop, zsel (u (ns (ms n))) ∈ Metric.closedBall α ε :=
      Eventually.of_forall fun n => le_of_lt (hzspec (u (ns (ms n)))).2
    exact hclosed.mem_of_tendsto hmstend hev
  have hw_eq : w = zsel x := by
    apply hisolate x w hwroot
    linarith
  change Tendsto ((fun n => zsel (u (ns n))) ∘ ms) atTop (nhds (zsel x))
  simpa [hw_eq] using hmstend

/-- The conjugate of a root of a polynomial with real coefficients is again a
    root. -/
theorem conj_root_of_real_coeff {Q : Polynomial ℂ} {d : ℕ} (hd : Q.natDegree = d)
    (hreal : ∀ k ≤ d, (Q.coeff k).im = 0) {w : ℂ} (hw : Q.IsRoot w) :
    Q.IsRoot ((starRingEnd ℂ) w) := by
  classical
  change Polynomial.eval ((starRingEnd ℂ) w) Q = 0
  rw [eval_eq_sum_fin (d := d) (by simp [hd]) ((starRingEnd ℂ) w)]
  have hwsum : (∑ k : Fin (d + 1), Q.coeff (k : ℕ) * w ^ (k : ℕ)) = 0 := by
    rw [← eval_eq_sum_fin (d := d) (by simp [hd]) w]
    exact hw
  have hstar : (starRingEnd ℂ) (∑ k : Fin (d + 1),
      Q.coeff (k : ℕ) * w ^ (k : ℕ)) =
      ∑ k : Fin (d + 1), Q.coeff (k : ℕ) * ((starRingEnd ℂ) w) ^ (k : ℕ) := by
    simp only [map_sum, map_mul, map_pow]
    apply Finset.sum_congr rfl
    intro k hk
    have hcstar : (starRingEnd ℂ) (Q.coeff (k : ℕ)) = Q.coeff (k : ℕ) := by
      rw [Complex.conj_eq_iff_im]
      exact hreal (k : ℕ) (Nat.le_of_lt_succ k.isLt)
    rw [hcstar]
  rw [← hstar, hwsum]
  simp

/-- A root isolated in a disc around a real centre is real. -/
theorem real_of_unique_root_in_real_ball
    {Q : Polynomial ℂ} {d : ℕ} (hd : Q.natDegree = d)
    (hreal : ∀ k ≤ d, (Q.coeff k).im = 0)
    {z w : ℂ} (hzreal : z.im = 0) (hroot : Q.IsRoot w)
    (hdist : dist w z < ε)
    (huniq : ∃! v : ℂ, Q.IsRoot v ∧ dist v z < ε) : w.im = 0 := by
  have hstarz : (starRingEnd ℂ) z = z := (Complex.conj_eq_iff_im).mpr hzreal
  have hcroot : Q.IsRoot ((starRingEnd ℂ) w) :=
    conj_root_of_real_coeff hd hreal hroot
  have hcdist : dist ((starRingEnd ℂ) w) z < ε := by
    have heqdist : dist ((starRingEnd ℂ) w) z = dist w z := by
      calc
        dist ((starRingEnd ℂ) w) z = dist ((starRingEnd ℂ) w) ((starRingEnd ℂ) z) := by rw [hstarz]
        _ = dist w z := Complex.dist_conj_conj w z
    rw [heqdist]
    exact hdist
  have hw_eq_choose : w = Classical.choose huniq :=
    (Classical.choose_spec huniq).2 w ⟨hroot, hdist⟩
  have heq : (starRingEnd ℂ) w = w := by
    have hc_eq_choose : (starRingEnd ℂ) w = Classical.choose huniq :=
      (Classical.choose_spec huniq).2 ((starRingEnd ℂ) w) ⟨hcroot, hcdist⟩
    exact hc_eq_choose.trans hw_eq_choose.symm
  exact (Complex.conj_eq_iff_im).mp heq

/-- Continuous root functions on a neighbourhood: for each distinct root of
    $p(x_0)$ there is a continuous function $g_z$ on a neighbourhood $U$ of
    $x_0$ such that $g_z(x)$ is the unique root of $p(x)$ in the disc around
    $z$. -/
theorem local_continuous_root_functions
    {X : Type*} [PseudoMetricSpace X]
    (p : X → Polynomial ℂ)
    (hcoeff : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (d m : ℕ) (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree = d)
    (hmonic : ∀ x, (p x).Monic)
    (hm : ∀ x, (p x).roots.toFinset.card = m)
    (x0 : X) :
    ∃ (U : Set X) (ε : ℝ) (g : ℂ → X → ℂ),
      IsOpen U ∧ x0 ∈ U ∧ 0 < ε ∧
      (∀ z ∈ (p x0).roots.toFinset, ContinuousOn (g z) U) ∧
      (∀ z ∈ (p x0).roots.toFinset, ∀ x ∈ U,
        (p x).IsRoot (g z x) ∧ dist (g z x) z < ε) ∧
      (∀ z ∈ (p x0).roots.toFinset, ∀ x ∈ U,
        ∃! w : ℂ, (p x).IsRoot w ∧ dist w z < ε) ∧
      (∀ x ∈ U, ∀ w ∈ (p x).roots.toFinset,
        ∃ z ∈ (p x0).roots.toFinset, dist w z < ε) ∧
      (∀ z ∈ (p x0).roots.toFinset, ∀ w ∈ (p x0).roots.toFinset,
        z ≠ w → 3 * ε < dist z w) := by
  classical
  obtain ⟨U, ε, hUopen, hx0U, hεpos, hsep4, huniq, hcover⟩ :=
    locally_unique_roots_of_monic_family p hcoeff d m hd hdeg hmonic hm x0
  let s := (p x0).roots.toFinset
  let g : ℂ → X → ℂ := fun z x =>
    if h : z ∈ s ∧ x ∈ U then Classical.choose (huniq z h.1 x h.2) else 0
  refine ⟨U, ε, g, hUopen, hx0U, hεpos, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hzs : z ∈ s := by simpa [s] using hz
    let fzx : X → ℂ := fun x =>
      if hx : x ∈ U then Classical.choose (huniq z hz x hx) else 0
    have hcont_sub : Continuous (fun x : U => Classical.choose (huniq z hz x.1 x.2)) := by
      let pU : U → Polynomial ℂ := fun x => p x.1
      have hcoeffU : ∀ k : ℕ, Continuous (fun x : U => (pU x).coeff k) := by
        intro k
        exact (hcoeff k).comp continuous_subtype_val
      have hdegU : ∀ x : U, (pU x).natDegree = d := fun x => hdeg x.1
      have hsel : ∀ x : U, ∃! w : ℂ, (pU x).IsRoot w ∧ dist w z < ε := by
        intro x
        exact huniq z hz x.1 x.2
      have hisolate : ∀ (x : U) (w : ℂ), (pU x).IsRoot w →
          dist w z < 2 * ε → w = Classical.choose (hsel x) := by
        intro x w hwroot hwdist
        have hwmemfin : w ∈ (p x.1).roots.toFinset :=
          Multiset.mem_toFinset.mpr
            ((Polynomial.mem_roots (hmonic x.1).ne_zero).mpr hwroot)
        rcases hcover x.1 x.2 w hwmemfin with ⟨z', hz's, hdistz'⟩
        have hzz' : z' = z := by
          by_contra hne
          have hneq : z ≠ z' := fun h => hne h.symm
          have hs' := hsep4 z hz z' (by simpa [s] using hz's) hneq
          have htri : dist z z' ≤ dist z w + dist w z' := dist_triangle _ _ _
          have hwdist' : dist z w < 2 * ε := by simpa [dist_comm] using hwdist
          linarith
        subst z'
        exact (Classical.choose_spec (huniq z hz x.1 x.2)).2 w ⟨hwroot, hdistz'⟩
      exact continuous_unique_root_in_ball pU hcoeffU d hdegU z ε hεpos hsel hisolate
    have hcont_fzx : ContinuousOn fzx U := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hcont_sub.congr (by intro x; simp [fzx, x.2])
    apply hcont_fzx.congr
    intro x hx
    simp [g, fzx, hzs, hx]
  · intro z hz x hx
    have hzs : z ∈ s := by simpa [s] using hz
    have hspec := (Classical.choose_spec (huniq z hz x hx)).1
    simpa [g, hzs, hx] using hspec
  · simpa [s] using huniq
  · simpa [s] using hcover
  · simpa [s] using hsep4

/-- If a continuous complex root branch passes through an isolated base root
    `z0`, and every nearby polynomial has a unique root in $B(z_0,\varepsilon)$,
    then the multiplicity of the branch is locally constant. -/
theorem rootMultiplicity_locally_constant_of_continuous_root_in_ball
    {X : Type*} [PseudoMetricSpace X]
    (p : X → Polynomial ℂ)
    (hcoeff : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree = d)
    (hmonic : ∀ x, (p x).Monic)
    (x0 : X) (z0 : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hz0root : (p x0).IsRoot z0)
    (hsep : ∀ β ∈ (p x0).roots.toFinset, β ≠ z0 → 2 * ε ≤ dist β z0)
    (U : Set X) (hUopen : IsOpen U) (hx0U : x0 ∈ U)
    (f : X → ℂ) (hf : ContinuousOn f U)
    (hfroot : ∀ x ∈ U, (p x).IsRoot (f x))
    (hf0 : f x0 = z0)
    (huniq : ∀ x ∈ U, ∃! w : ℂ, (p x).IsRoot w ∧ dist w z0 < ε) :
    ∃ V : Set X, IsOpen V ∧ x0 ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, Polynomial.rootMultiplicity (f x) (p x) =
        Polynomial.rootMultiplicity z0 (p x0) := by
  classical
  obtain ⟨δ, hδpos, hδprop⟩ := roots_count_in_ball_eq_of_coeff_close
    (p x0) (hmonic x0) (by simpa [hdeg x0] using hd) z0 hz0root ε hε hsep
  let Vcoeff : Set X := {y | ∀ k : Fin (d + 1),
    ‖(p y).coeff (k : ℕ) - (p x0).coeff (k : ℕ)‖ < δ}
  have hVcoeffopen : IsOpen Vcoeff := by
    dsimp [Vcoeff]
    have h : IsOpen (⋂ k : Fin (d + 1),
        {y : X | ‖(p y).coeff (k : ℕ) - (p x0).coeff (k : ℕ)‖ < δ}) := by
      apply isOpen_iInter_of_finite
      intro k
      exact isOpen_lt ((hcoeff (k : ℕ)).sub continuous_const).norm continuous_const
    have hset : (⋂ k : Fin (d + 1),
        {y : X | ‖(p y).coeff (k : ℕ) - (p x0).coeff (k : ℕ)‖ < δ}) =
        {y : X | ∀ k : Fin (d + 1),
          ‖(p y).coeff (k : ℕ) - (p x0).coeff (k : ℕ)‖ < δ} := by
      ext y
      simp
    rw [← hset]
    exact h
  have hx0Vcoeff : x0 ∈ Vcoeff := by
    intro k
    simp
    exact hδpos
  have hUball : IsOpen (U ∩ {y | dist (f y) z0 < ε}) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hfy : ContinuousAt f y := hf.continuousAt (hUopen.mem_nhds hy.1)
    have hball : {y | dist (f y) z0 < ε} ∈ nhds y := by
      rw [show {y | dist (f y) z0 < ε} = f ⁻¹' Metric.ball z0 ε by
        ext y
        simp]
      exact hfy.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hy.2)
    exact inter_mem (hUopen.mem_nhds hy.1) hball
  let V : Set X := (U ∩ {y | dist (f y) z0 < ε}) ∩ Vcoeff
  have hVopen : IsOpen V := hUball.inter hVcoeffopen
  have hx0V : x0 ∈ V := by
    refine ⟨⟨hx0U, ?_⟩, hx0Vcoeff⟩
    simpa [hf0] using hε
  refine ⟨V, hVopen, hx0V, ?_, ?_⟩
  · intro y hy
    exact hy.1.1
  · intro y hy
    rcases hy with ⟨⟨hyU, hydist⟩, hyVcoeff⟩
    have hclose : ∀ k ≤ d, ‖(p y).coeff k - (p x0).coeff k‖ < δ := by
      intro k hk
      exact hyVcoeff ⟨k, by omega⟩
    have hclose' : ∀ k ≤ (p x0).natDegree,
        ‖(p y).coeff k - (p x0).coeff k‖ < δ := by
      intro k hk
      exact hclose k (by simpa [hdeg x0] using hk)
    have hcnt := hδprop (p y) (hmonic y) (by rw [hdeg y, hdeg x0]) hclose'
    have huniqy := huniq y hyU
    have hfyeq : f y = Classical.choose huniqy :=
      (Classical.choose_spec huniqy).2 (f y) ⟨hfroot y hyU, hydist⟩
    have hfilter : (p y).roots.filter (fun w => dist w z0 < ε) =
        (p y).roots.filter (fun w => w = Classical.choose huniqy) := by
      apply Multiset.filter_congr
      intro w hw
      constructor
      · intro hwdist
        have hwroot : (p y).IsRoot w := Polynomial.isRoot_of_mem_roots hw
        exact (Classical.choose_spec huniqy).2 w ⟨hwroot, hwdist⟩
      · intro heq
        subst w
        exact (Classical.choose_spec huniqy).1.2
    have hcard : ((p y).roots.filter (fun w => dist w z0 < ε)).card =
        (p y).roots.count (Classical.choose huniqy) := by
      rw [hfilter, Multiset.filter_eq']
      simp
    rw [← Polynomial.count_roots (a := f y) (p y)]
    rw [hfyeq]
    rw [← hcard]
    rw [hcnt]
    rw [← Polynomial.count_roots (a := z0) (p x0)]

/-- A real root at the base point stays real along a nearby continuous family
    of real-coefficient polynomials. -/
theorem local_real_root_functions
    {X : Type*} [PseudoMetricSpace X]
    (p : X → Polynomial ℂ)
    (hcoeff : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (d m : ℕ) (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree = d)
    (hmonic : ∀ x, (p x).Monic)
    (hm : ∀ x, (p x).roots.toFinset.card = m)
    (hreal : ∀ x k, ((p x).coeff k).im = 0)
    (x0 : X) :
    ∃ (U : Set X) (ε : ℝ) (g : ℂ → X → ℂ),
      IsOpen U ∧ x0 ∈ U ∧ 0 < ε ∧
      (∀ z' ∈ (p x0).roots.toFinset, ContinuousOn (g z') U) ∧
      (∀ z' ∈ (p x0).roots.toFinset, ∀ x ∈ U,
        (p x).IsRoot (g z' x) ∧ dist (g z' x) z' < ε) ∧
      (∀ z' ∈ (p x0).roots.toFinset, z'.im = 0 → ∀ x ∈ U,
        (g z' x).im = 0) ∧
      (∀ x ∈ U, ∀ w ∈ (p x).roots.toFinset,
        ∃ z' ∈ (p x0).roots.toFinset, dist w z' < ε) ∧
      (∀ z ∈ (p x0).roots.toFinset, ∀ w ∈ (p x0).roots.toFinset,
        z ≠ w → 3 * ε < dist z w) ∧
      (∀ z ∈ (p x0).roots.toFinset, ∀ x ∈ U,
        ∃! w : ℂ, (p x).IsRoot w ∧ dist w z < ε) := by
  obtain ⟨U, ε, g, hUopen, hx0U, hεpos, hcont, hrootprop, huniq, hcover, hsep4'⟩ :=
    local_continuous_root_functions p hcoeff d m hd hdeg hmonic hm x0
  refine ⟨U, ε, g, hUopen, hx0U, hεpos, hcont, hrootprop, ?_, hcover, ?_, huniq⟩
  intro z hz hzreal x hx
  have hspec := hrootprop z hz x hx
  exact real_of_unique_root_in_real_ball (Q := p x) (d := d) (hdeg x)
    (fun k hk => hreal x k) hzreal hspec.1 hspec.2 (huniq z hz x hx)
  · simpa using hsep4'

/-- The number of distinct real roots is locally constant. -/
theorem real_root_count_locally_constant
    {X : Type*} [PseudoMetricSpace X]
    (p : X → Polynomial ℂ)
    (hcoeff : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (d m : ℕ) (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree = d)
    (hmonic : ∀ x, (p x).Monic)
    (hm : ∀ x, (p x).roots.toFinset.card = m)
    (hreal : ∀ x k, ((p x).coeff k).im = 0)
    (x0 : X) :
    ∃ U : Set X, IsOpen U ∧ x0 ∈ U ∧ ∀ x ∈ U,
      ((p x).roots.toFinset.filter (fun z => z.im = 0)).card =
      ((p x0).roots.toFinset.filter (fun z => z.im = 0)).card := by
  classical
  obtain ⟨U, ε, g, hUopen, hx0U, hεpos, _hcont, hrootprop, hrealpres,
    hcover, hsep4, huniq⟩ :=
    local_real_root_functions p hcoeff d m hd hdeg hmonic hm hreal x0
  refine ⟨U, hUopen, hx0U, ?_⟩
  intro x hx
  let S0 := (p x0).roots.toFinset.filter (fun z => z.im = 0)
  let Sx := (p x).roots.toFinset.filter (fun z => z.im = 0)
  have hcard0 : S0.card = Sx.card := by
    refine Finset.card_bij (s := S0) (t := Sx) (fun z _ => g z x) ?_ ?_ ?_
    · intro z hz
      have hzS : z ∈ (p x0).roots.toFinset := (Finset.mem_filter.mp hz).1
      have hzreal : z.im = 0 := (Finset.mem_filter.mp hz).2
      have hg := hrootprop z hzS x hx
      have hgreal := hrealpres z hzS hzreal x hx
      exact Finset.mem_filter.mpr ⟨
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hmonic x).ne_zero).mpr hg.1),
        hgreal⟩
    · intro z1 hz1 z2 hz2 heq
      have hz1S : z1 ∈ (p x0).roots.toFinset := (Finset.mem_filter.mp hz1).1
      have hz2S : z2 ∈ (p x0).roots.toFinset := (Finset.mem_filter.mp hz2).1
      by_contra hne
      have hs' := hsep4 z1 hz1S z2 hz2S hne
      have hd1 := (hrootprop z1 hz1S x hx).2
      have hd2 := (hrootprop z2 hz2S x hx).2
      have htri : dist z1 z2 ≤ dist z1 (g z1 x) + dist (g z1 x) z2 := dist_triangle _ _ _
      rw [← heq] at hd2
      have hd1' : dist z1 (g z1 x) < ε := by simpa [dist_comm] using hd1
      linarith
    · intro w hw
      have hwrootmem : w ∈ (p x).roots.toFinset := (Finset.mem_filter.mp hw).1
      have hwreal : w.im = 0 := (Finset.mem_filter.mp hw).2
      have hwroot : (p x).IsRoot w :=
        Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hwrootmem)
      rcases hcover x hx w hwrootmem with ⟨z, hzS, hdist⟩
      have hzreal : z.im = 0 := by
        by_contra hnreal
        have hcz := conj_root_of_real_coeff (hd := hdeg x0)
          (fun k hk => hreal x0 k) (Polynomial.isRoot_of_mem_roots
            (Multiset.mem_toFinset.mp hzS))
        have hczmem : (starRingEnd ℂ) z ∈ (p x0).roots.toFinset :=
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hmonic x0).ne_zero).mpr hcz)
        have hneq : (starRingEnd ℂ) z ≠ z := by
          intro heq
          exact hnreal ((Complex.conj_eq_iff_im).mp heq)
        have hs' := hsep4 z hzS ((starRingEnd ℂ) z) hczmem hneq.symm
        have hstarw : (starRingEnd ℂ) w = w := (Complex.conj_eq_iff_im).mpr hwreal
        have hdistcw : dist w ((starRingEnd ℂ) z) = dist w z := by
          rw [← Complex.dist_conj_comm w z, hstarw]
        have htri : dist z ((starRingEnd ℂ) z) ≤ dist z w + dist w ((starRingEnd ℂ) z) :=
          dist_triangle _ _ _
        rw [hdistcw] at htri
        rw [dist_comm z w] at htri
        linarith
      refine ⟨z, Finset.mem_filter.mpr ⟨hzS, hzreal⟩, ?_⟩
      have hwball := (huniq z hzS x hx)
      have hg := hrootprop z hzS x hx
      have hgz : g z x = Classical.choose hwball :=
        (Classical.choose_spec hwball).2 (g z x) ⟨hg.1, hg.2⟩
      rw [hgz]
      exact (Classical.choose_spec hwball).2 w ⟨hwroot, hdist⟩ |>.symm
  simpa [Sx, S0] using hcard0.symm

/-- On a preconnected space the number of distinct real roots is constant. -/
theorem real_root_count_constant_on_preconnected
    {X : Type*} [PseudoMetricSpace X] [PreconnectedSpace X]
    (p : X → Polynomial ℂ)
    (hcoeff : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (d m : ℕ) (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree = d)
    (hmonic : ∀ x, (p x).Monic)
    (hm : ∀ x, (p x).roots.toFinset.card = m)
    (hreal : ∀ x k, ((p x).coeff k).im = 0) :
    ∀ x y : X,
      ((p x).roots.toFinset.filter (fun z => z.im = 0)).card =
      ((p y).roots.toFinset.filter (fun z => z.im = 0)).card := by
  classical
  let c : X → ℕ := fun x => ((p x).roots.toFinset.filter (fun z => z.im = 0)).card
  have hloc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨U, hUopen, hxU, hconst⟩ :=
      real_root_count_locally_constant p hcoeff d m hd hdeg hmonic hm hreal x
    exact ⟨U, hUopen, hxU, fun y hy => hconst y hy⟩
  intro x y
  exact hloc.apply_eq_of_preconnectedSpace x y

end CollinsCAD
