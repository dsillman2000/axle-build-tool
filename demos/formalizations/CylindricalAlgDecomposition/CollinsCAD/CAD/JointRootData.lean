import Mathlib
import CAD.LocalRootData

namespace CollinsCAD

open Polynomial Filter

/-- An open set on which a continuous-on-`U` function stays in a fixed ball is
    relatively open in `U`. -/
theorem isOpen_inter_dist_lt {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (hU : IsOpen U) {f : X → ℂ} (hf : ContinuousOn f U)
    (z : ℂ) (ε : ℝ) : IsOpen (U ∩ {x | dist (f x) z < ε}) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hfx : ContinuousAt f x := hf.continuousAt (hU.mem_nhds hx.1)
  have hball : {y | dist (f y) z < ε} ∈ nhds x := by
    rw [show {y | dist (f y) z < ε} = f ⁻¹' Metric.ball z ε by
      ext y
      simp]
    exact hfx.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hx.2)
  exact inter_mem (hU.mem_nhds hx.1) hball

/-- Joint local complex root data for two polynomial families. -/
structure JointRootData {X : Type*} [PseudoMetricSpace X]
    (p q : X → Polynomial ℂ) (x₀ : X) where
  U : Set X
  ε : ℝ
  gp : ℂ → X → ℂ
  gq : ℂ → X → ℂ
  ep : ℂ → ℕ
  eq : ℂ → ℕ
  hU : IsOpen U
  hx₀ : x₀ ∈ U
  hε : 0 < ε
  hp : RootBranchesOn p x₀ U ε gp ep
  hq : RootBranchesOn q x₀ U ε gq eq
  hcross : ∀ z ∈ (p x₀).roots.toFinset, ∀ w ∈ (q x₀).roots.toFinset,
    z ≠ w → 3 * ε < dist z w

/-- Two local root packages can be shrunk to a common separating radius. -/
theorem exists_jointRootData {X : Type*} [PseudoMetricSpace X]
    (p q : X → Polynomial ℂ) (x₀ : X)
    (hp : Nonempty (LocalRootData p x₀)) (hq : Nonempty (LocalRootData q x₀)) :
    Nonempty (JointRootData p q x₀) := by
  classical
  let Jp := Classical.choice hp
  let Jq := Classical.choice hq
  let s := (p x₀).roots.toFinset ∪ (q x₀).roots.toFinset
  obtain ⟨ε₀, hε₀, hsep₀⟩ := exists_separation_radius s
  let ε : ℝ := min Jp.ε (min Jq.ε (ε₀ / 2))
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min Jp.hε (lt_min Jq.hε (by linarith))
  have hεp : ε ≤ Jp.ε := min_le_left _ _
  have hεq : ε ≤ Jq.ε := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεsep : ε ≤ ε₀ / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  let Vp : Set X := ⋂ z : (p x₀).roots.toFinset,
    (Jp.U ∩ {x | dist (Jp.g z.1 x) z.1 < ε})
  let Vq : Set X := ⋂ z : (q x₀).roots.toFinset,
    (Jq.U ∩ {x | dist (Jq.g z.1 x) z.1 < ε})
  let U : Set X := Jp.U ∩ Jq.U ∩ Vp ∩ Vq
  have hVpopen : IsOpen Vp := by
    apply isOpen_iInter_of_finite
    intro z
    exact isOpen_inter_dist_lt Jp.hU (Jp.branches.hcont z.1 z.2) z.1 ε
  have hVqopen : IsOpen Vq := by
    apply isOpen_iInter_of_finite
    intro z
    exact isOpen_inter_dist_lt Jq.hU (Jq.branches.hcont z.1 z.2) z.1 ε
  have hUopen : IsOpen U := by
    exact ((Jp.hU.inter Jq.hU).inter hVpopen).inter hVqopen
  have hx0U : x₀ ∈ U := by
    refine ⟨⟨⟨Jp.hx₀, Jq.hx₀⟩, ?_⟩, ?_⟩
    · simp only [Vp, Set.mem_iInter]
      intro z
      exact ⟨Jp.hx₀, by simpa [Jp.branches.hbase z.1 z.2] using hε⟩
    · simp only [Vq, Set.mem_iInter]
      intro z
      exact ⟨Jq.hx₀, by simpa [Jq.branches.hbase z.1 z.2] using hε⟩
  have hUp : U ⊆ Jp.U := fun _ hx => hx.1.1.1
  have hUq : U ⊆ Jq.U := fun _ hx => hx.1.1.2
  have hp' : RootBranchesOn p x₀ U ε Jp.g Jp.e := by
    constructor
    · intro x hx
      exact Jp.branches.hne x (hUp hx)
    · intro z hz
      exact (Jp.branches.hcont z hz).mono hUp
    · intro z hz x hx
      have h := Jp.branches.hroot z hz x (hUp hx)
      have hnear : dist (Jp.g z x) z < ε :=
        (Set.mem_iInter.mp hx.1.2 ⟨z, hz⟩).2
      exact ⟨h.1, hnear, h.2.2⟩
    · exact Jp.branches.hepos
    · exact Jp.branches.hbase
    · intro x hx w hw
      exact Jp.branches.hcover x (hUp hx) w hw
    · intro z hz w hw hzw
      exact lt_of_le_of_lt (by linarith : 3 * ε ≤ 3 * Jp.ε)
        (Jp.branches.hsep z hz w hw hzw)
  have hq' : RootBranchesOn q x₀ U ε Jq.g Jq.e := by
    constructor
    · intro x hx
      exact Jq.branches.hne x (hUq hx)
    · intro z hz
      exact (Jq.branches.hcont z hz).mono hUq
    · intro z hz x hx
      have h := Jq.branches.hroot z hz x (hUq hx)
      have hnear : dist (Jq.g z x) z < ε :=
        (Set.mem_iInter.mp hx.2 ⟨z, hz⟩).2
      exact ⟨h.1, hnear, h.2.2⟩
    · exact Jq.branches.hepos
    · exact Jq.branches.hbase
    · intro x hx w hw
      exact Jq.branches.hcover x (hUq hx) w hw
    · intro z hz w hw hzw
      exact lt_of_le_of_lt (by linarith : 3 * ε ≤ 3 * Jq.ε)
        (Jq.branches.hsep z hz w hw hzw)
  have hcross : ∀ z ∈ (p x₀).roots.toFinset, ∀ w ∈ (q x₀).roots.toFinset,
      z ≠ w → 3 * ε < dist z w := by
    intro z hz w hw hzw
    have hzunion : z ∈ s := Finset.mem_union_left _ hz
    have hwunion : w ∈ s := Finset.mem_union_right _ hw
    have hs := hsep₀ z hzunion w hwunion hzw
    linarith
  exact ⟨⟨U, ε, Jp.g, Jq.g, Jp.e, Jq.e, hUopen, hx0U, hε,
    hp', hq', hcross⟩⟩

/-- Every common nearby root is represented by the same seated base root in
    both local branch systems. -/
theorem JointRootData.common_root_eq {X : Type*} [PseudoMetricSpace X]
    {p q : X → Polynomial ℂ} {x₀ : X} (J : JointRootData p q x₀)
    {x : X} (hx : x ∈ J.U) {w : ℂ}
    (hpw : (p x).IsRoot w) (hqw : (q x).IsRoot w) :
    ∃ α ∈ commonRootFinset (p x₀) (q x₀),
      J.gp α x = w ∧ J.gq α x = w := by
  classical
  have hwpmem : w ∈ (p x).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (J.hp.hne x hx)).mpr hpw)
  have hwqmem : w ∈ (q x).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (J.hq.hne x hx)).mpr hqw)
  rcases J.hp.hcover x hx w hwpmem with ⟨z, hz, hgp⟩
  rcases J.hq.hcover x hx w hwqmem with ⟨z', hz', hgq⟩
  have hzz' : z = z' := by
    by_contra hne
    have hcross := J.hcross z hz z' hz' hne
    have hdz := (J.hp.hroot z hz x hx).2.1
    have hdz' := (J.hq.hroot z' hz' x hx).2.1
    rw [hgp] at hdz
    rw [hgq] at hdz'
    have htri : dist z z' ≤ dist z w + dist w z' := dist_triangle _ _ _
    rw [dist_comm w z] at hdz
    have hεpos := J.hε
    linarith
  subst z'
  exact ⟨z, Finset.mem_inter.mpr ⟨hz, hz'⟩, hgp, hgq⟩

/-- A nearby root in a seated disc is the corresponding local branch. -/
theorem JointRootData.eq_gp_of_root_near {X : Type*} [PseudoMetricSpace X]
    {p q : X → Polynomial ℂ} {x₀ : X} (J : JointRootData p q x₀)
    {x : X} (hx : x ∈ J.U) {α w : ℂ}
    (hα : α ∈ (p x₀).roots.toFinset)
    (hw : (p x).IsRoot w) (hnear : dist w α < J.ε) : w = J.gp α x := by
  classical
  have hwmem : w ∈ (p x).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (J.hp.hne x hx)).mpr hw)
  rcases J.hp.hcover x hx w hwmem with ⟨z, hz, hgz⟩
  have hzα : z = α := by
    by_contra hne
    have hsep := J.hp.hsep z hz α hα hne
    have hdz := (J.hp.hroot z hz x hx).2.1
    rw [hgz] at hdz
    rw [dist_comm w z] at hdz
    have htri : dist z α ≤ dist z w + dist w α := dist_triangle _ _ _
    have hεpos := J.hε
    linarith
  subst z
  exact hgz.symm

/-- A nearby root in a seated disc is the corresponding local branch. -/
theorem JointRootData.eq_gq_of_root_near {X : Type*} [PseudoMetricSpace X]
    {p q : X → Polynomial ℂ} {x₀ : X} (J : JointRootData p q x₀)
    {x : X} (hx : x ∈ J.U) {α w : ℂ}
    (hα : α ∈ (q x₀).roots.toFinset)
    (hw : (q x).IsRoot w) (hnear : dist w α < J.ε) : w = J.gq α x := by
  classical
  have hwmem : w ∈ (q x).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (J.hq.hne x hx)).mpr hw)
  rcases J.hq.hcover x hx w hwmem with ⟨z, hz, hgz⟩
  have hzα : z = α := by
    by_contra hne
    have hsep := J.hq.hsep z hz α hα hne
    have hdz := (J.hq.hroot z hz x hx).2.1
    rw [hgz] at hdz
    rw [dist_comm w z] at hdz
    have htri : dist z α ≤ dist z w + dist w α := dist_triangle _ _ _
    have hεpos := J.hε
    linarith
  subst z
  exact hgz.symm

end CollinsCAD
