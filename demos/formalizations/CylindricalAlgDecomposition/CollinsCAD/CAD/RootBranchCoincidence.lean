import Mathlib
import CAD.JointGcdDegree

namespace CollinsCAD

open Polynomial Filter

/-- If two continuous real root branches belong to monic complex families with
    constant GCD degree, their coincidence set is clopen. -/
theorem isClopen_rootBranch_eq_of_gcdNatDegree_const
    {X : Type*} [PseudoMetricSpace X]
    (p q : X → Polynomial ℂ)
    (hcoeffP : ∀ k : ℕ, Continuous (fun x => (p x).coeff k))
    (hcoeffQ : ∀ k : ℕ, Continuous (fun x => (q x).coeff k))
    (dP mP dQ mQ : ℕ)
    (hdP : 0 < dP) (hdQ : 0 < dQ)
    (hdegP : ∀ x, (p x).natDegree = dP)
    (hdegQ : ∀ x, (q x).natDegree = dQ)
    (hmonicP : ∀ x, (p x).Monic)
    (hmonicQ : ∀ x, (q x).Monic)
    (hmP : ∀ x, (p x).roots.toFinset.card = mP)
    (hmQ : ∀ x, (q x).roots.toFinset.card = mQ)
    (hD : ∀ x y, gcdNatDegree (p x) (q x) = gcdNatDegree (p y) (q y))
    (f g : X → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfroot : ∀ x, (p x).IsRoot ((f x : ℝ) : ℂ))
    (hgroot : ∀ x, (q x).IsRoot ((g x : ℝ) : ℂ)) :
    IsClopen {x | f x = g x} := by
  classical
  constructor
  · exact isClosed_eq hf hg
  · rw [isOpen_iff_mem_nhds]
    intro x₀ hx₀
    let α : ℂ := ((f x₀ : ℝ) : ℂ)
    have hx0eq : f x₀ = g x₀ := hx₀
    have hαp : α ∈ (p x₀).roots.toFinset := by
      exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots (hmonicP x₀).ne_zero).mpr (hfroot x₀))
    have hαq : α ∈ (q x₀).roots.toFinset := by
      have hfg : ((g x₀ : ℝ) : ℂ) = α := by simp [α, hx0eq]
      rw [← hfg]
      exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots (hmonicQ x₀).ne_zero).mpr (hgroot x₀))
    obtain ⟨J⟩ := exists_jointRootData p q x₀
      (exists_localRootData p hcoeffP dP mP hdP hdegP hmonicP hmP x₀)
      (exists_localRootData q hcoeffQ dQ mQ hdQ hdegQ hmonicQ hmQ x₀)
    have hαcommon : α ∈ commonRootFinset (p x₀) (q x₀) :=
      Finset.mem_inter.mpr ⟨hαp, hαq⟩
    have hcoinc := JointRootData.branch_eq_of_gcdNatDegree_const J hD hαcommon
    let Vf : Set X := {x | dist ((f x : ℝ) : ℂ) α < J.ε}
    let Vg : Set X := {x | dist ((g x : ℝ) : ℂ) α < J.ε}
    have hVf : IsOpen Vf := by
      dsimp [Vf]
      exact isOpen_lt (by fun_prop) continuous_const
    have hVg : IsOpen Vg := by
      dsimp [Vg]
      exact isOpen_lt (by fun_prop) continuous_const
    have hx0V : x₀ ∈ J.U ∩ Vf ∩ Vg := by
      refine ⟨⟨J.hx₀, ?_⟩, ?_⟩ <;> simp [Vf, Vg, α, J.hε, hx0eq]
    refine Filter.mem_of_superset
      (((J.hU.inter hVf).inter hVg).mem_nhds hx0V) (by
        intro y hy
        have hyU := hy.1.1
        have hyf := hy.1.2
        have hyg := hy.2
        have hfy : ((f y : ℝ) : ℂ) = J.gp α y :=
          JointRootData.eq_gp_of_root_near J hyU hαp (hfroot y) hyf
        have hgy : ((g y : ℝ) : ℂ) = J.gq α y :=
          JointRootData.eq_gq_of_root_near J hyU hαq (hgroot y) hyg
        apply Complex.ofReal_injective
        exact hfy.trans ((hcoinc y hyU).trans hgy.symm))

/-- On a preconnected space, a clopen coincidence set is either everything or
    empty. -/
theorem rootBranch_eq_or_ne_of_isClopen {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {f g : X → ℝ}
    (hcl : IsClopen {x | f x = g x}) :
    (∀ x, f x = g x) ∨ (∀ x, f x ≠ g x) := by
  rcases isClopen_iff.mp hcl with hEmpty | hUniv
  · right
    intro x hxe
    have hx : x ∈ ({x | f x = g x} : Set X) := hxe
    rw [hEmpty] at hx
    exact hx
  · left
    intro x
    have hx : x ∈ ({x | f x = g x} : Set X) := by
      rw [hUniv]
      trivial
    exact hx

end CollinsCAD
