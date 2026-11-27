import Mathlib
import Analysis.LocalRoots
import CAD.CommonRoots

namespace CollinsCAD

open Polynomial Filter

/-- Continuous complex root branches seated at the roots of a base fibre. -/
structure RootBranchesOn {X : Type*} [PseudoMetricSpace X]
    (p : X → Polynomial ℂ) (x₀ : X)
    (U : Set X) (ε : ℝ) (g : ℂ → X → ℂ) (e : ℂ → ℕ) : Prop where
  hne : ∀ x ∈ U, p x ≠ 0
  hcont : ∀ z ∈ (p x₀).roots.toFinset, ContinuousOn (g z) U
  hroot : ∀ z ∈ (p x₀).roots.toFinset, ∀ x ∈ U,
    (p x).IsRoot (g z x) ∧ dist (g z x) z < ε ∧
      Polynomial.rootMultiplicity (g z x) (p x) = e z
  hepos : ∀ z ∈ (p x₀).roots.toFinset, 0 < e z
  hbase : ∀ z ∈ (p x₀).roots.toFinset, g z x₀ = z
  hcover : ∀ x ∈ U, ∀ w ∈ (p x).roots.toFinset,
    ∃ z ∈ (p x₀).roots.toFinset, g z x = w
  hsep : ∀ z ∈ (p x₀).roots.toFinset, ∀ w ∈ (p x₀).roots.toFinset,
    z ≠ w → 3 * ε < dist z w

/-- A local package of complex root branches with constant multiplicities. -/
structure LocalRootData {X : Type*} [PseudoMetricSpace X]
    (p : X → Polynomial ℂ) (x₀ : X) where
  U : Set X
  ε : ℝ
  g : ℂ → X → ℂ
  e : ℂ → ℕ
  hU : IsOpen U
  hx₀ : x₀ ∈ U
  hε : 0 < ε
  branches : RootBranchesOn p x₀ U ε g e

/-- Every monic family of constant degree and distinct-root count has local
    complex root data with constant multiplicities. -/
theorem exists_localRootData {X : Type*} [PseudoMetricSpace X]
    (p : X → Polynomial ℂ)
    (hcoeff : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (d m : ℕ) (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree = d)
    (hmonic : ∀ x, (p x).Monic)
    (hm : ∀ x, (p x).roots.toFinset.card = m)
    (x₀ : X) : Nonempty (LocalRootData p x₀) := by
  classical
  obtain ⟨U, ε, g, hUopen, hx0U, hεpos, hcont, hrootprop, huniq, hcover, hsep4⟩ :=
    local_continuous_root_functions p hcoeff d m hd hdeg hmonic hm x₀
  have hgbase : ∀ z ∈ (p x₀).roots.toFinset, g z x₀ = z := by
    intro z hz
    have hzroot : (p x₀).IsRoot z :=
      Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hz)
    have hgzroot := (hrootprop z hz x₀ hx0U).1
    have hgznear := (hrootprop z hz x₀ hx0U).2
    have hchoose_z := (Classical.choose_spec (huniq z hz x₀ hx0U)).2 z
      ⟨hzroot, by simpa using hεpos⟩
    have hchoose_g := (Classical.choose_spec (huniq z hz x₀ hx0U)).2 (g z x₀)
      ⟨hgzroot, hgznear⟩
    exact hchoose_g.trans hchoose_z.symm
  have hmult : ∀ z : (p x₀).roots.toFinset,
      ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
        ∀ x ∈ V, Polynomial.rootMultiplicity (g z.1 x) (p x) =
          Polynomial.rootMultiplicity z.1 (p x₀) := by
    intro z
    have hz : z.1 ∈ (p x₀).roots.toFinset := z.2
    have hzroot : (p x₀).IsRoot z.1 :=
      Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hz)
    have hsepz : ∀ β ∈ (p x₀).roots.toFinset, β ≠ z.1 →
        2 * ε ≤ dist β z.1 := by
      intro β hβ hβz
      have hs := hsep4 z.1 hz β hβ (Ne.symm hβz)
      rw [dist_comm]
      linarith
    exact rootMultiplicity_locally_constant_of_continuous_root_in_ball
      p hcoeff d hd hdeg hmonic x₀ z.1 ε hεpos hzroot hsepz
      U hUopen hx0U (g z.1) (hcont z.1 hz)
      (fun x hx => (hrootprop z.1 hz x hx).1) (hgbase z.1 hz)
      (fun x hx => huniq z.1 hz x hx)
  let Vfun : (p x₀).roots.toFinset → Set X := fun z => Classical.choose (hmult z)
  have hVfun : ∀ z : (p x₀).roots.toFinset,
      IsOpen (Vfun z) ∧ x₀ ∈ Vfun z ∧ Vfun z ⊆ U ∧
        ∀ x ∈ Vfun z, Polynomial.rootMultiplicity (g z.1 x) (p x) =
          Polynomial.rootMultiplicity z.1 (p x₀) := by
    intro z
    exact Classical.choose_spec (hmult z)
  let V : Set X := U ∩ ⋂ z : (p x₀).roots.toFinset, Vfun z
  have hVopen : IsOpen V := by
    apply hUopen.inter
    apply isOpen_iInter_of_finite
    intro z
    exact (hVfun z).1
  have hx0V : x₀ ∈ V := by
    refine ⟨hx0U, ?_⟩
    simp only [Set.mem_iInter]
    intro z
    exact (hVfun z).2.1
  have hVU : V ⊆ U := fun _ hx => hx.1
  let e : ℂ → ℕ := fun z => Polynomial.rootMultiplicity z (p x₀)
  refine ⟨⟨V, ε, g, e, hVopen, hx0V, hεpos, ?_⟩⟩
  constructor
  · intro x hx
    exact (hmonic x).ne_zero
  · intro z hz
    exact (hcont z hz).mono hVU
  · intro z hz x hx
    have hxVfun : x ∈ Vfun ⟨z, hz⟩ := by
      have hx' := hx.2
      simp only [Set.mem_iInter] at hx'
      exact hx' ⟨z, hz⟩
    have hmultx := (hVfun ⟨z, hz⟩).2.2.2 x hxVfun
    exact ⟨(hrootprop z hz x (hVU hx)).1,
      (hrootprop z hz x (hVU hx)).2, hmultx⟩
  · intro z hz
    dsimp [e]
    exact (Polynomial.rootMultiplicity_pos (hmonic x₀).ne_zero).mpr
      (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hz))
  · intro z hz
    exact hgbase z hz
  · intro x hx w hw
    rcases hcover x (hVU hx) w hw with ⟨z, hz, hdist⟩
    refine ⟨z, hz, ?_⟩
    have hwroot : (p x).IsRoot w :=
      Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hw)
    have hgzroot := (hrootprop z hz x (hVU hx)).1
    have hgznear := (hrootprop z hz x (hVU hx)).2
    have hchoose_g := (Classical.choose_spec (huniq z hz x (hVU hx))).2 (g z x)
      ⟨hgzroot, hgznear⟩
    have hchoose_w := (Classical.choose_spec (huniq z hz x (hVU hx))).2 w
      ⟨hwroot, hdist⟩
    exact hchoose_g.trans hchoose_w.symm
  · intro z hz w hw hzw
    exact hsep4 z hz w hw hzw

end CollinsCAD
