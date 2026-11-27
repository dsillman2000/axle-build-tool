import Mathlib
import CAD.JointRootData

namespace CollinsCAD

open Polynomial Filter
open scoped BigOperators

/-- On a joint root neighbourhood, GCD degree is the sum of the multiplicities
    of exactly those seated common branches that still coincide. -/
theorem JointRootData.gcdNatDegree_eq {X : Type*} [PseudoMetricSpace X]
    {p q : X → Polynomial ℂ} {x₀ : X} (J : JointRootData p q x₀)
    {x : X} (hx : x ∈ J.U) :
    gcdNatDegree (p x) (q x) =
      ∑ α ∈ commonRootFinset (p x₀) (q x₀),
        if J.gp α x = J.gq α x then min (J.ep α) (J.eq α) else 0 := by
  classical
  have hpne := J.hp.hne x hx
  have hqne := J.hq.hne x hx
  have hG : EuclideanDomain.gcd (p x) (q x) ≠ 0 := by
    intro hz
    have hdvd := EuclideanDomain.gcd_dvd_left (p x) (q x)
    rw [hz] at hdvd
    exact hpne (zero_dvd_iff.mp hdvd)
  let s := (commonRootFinset (p x₀) (q x₀)).filter
    (fun α => J.gp α x = J.gq α x)
  calc
    gcdNatDegree (p x) (q x) =
        ∑ w ∈ (EuclideanDomain.gcd (p x) (q x)).roots.toFinset,
          Polynomial.rootMultiplicity w (EuclideanDomain.gcd (p x) (q x)) := by
      simpa [gcdNatDegree] using
        natDegree_eq_sum_rootMultiplicity (EuclideanDomain.gcd (p x) (q x))
    _ = ∑ α ∈ s, min (J.ep α) (J.eq α) := by
      symm
      apply Finset.sum_bij (fun α _ => J.gp α x)
      · intro α hα
        have hα' := Finset.mem_filter.mp hα
        have hαp := (Finset.mem_inter.mp hα'.1).1
        have hαq := (Finset.mem_inter.mp hα'.1).2
        have hpα := (J.hp.hroot α hαp x hx).1
        have hqα := (J.hq.hroot α hαq x hx).1
        rw [← hα'.2] at hqα
        have hwG : (EuclideanDomain.gcd (p x) (q x)).IsRoot (J.gp α x) :=
          Polynomial.isRoot_gcd_iff_isRoot_left_right.mpr ⟨hpα, hqα⟩
        exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hG).mpr hwG)
      · intro α₁ hα₁ α₂ hα₂ heq
        have hα₁' := Finset.mem_filter.mp hα₁
        have hα₂' := Finset.mem_filter.mp hα₂
        by_contra hne
        have hα₁p := (Finset.mem_inter.mp hα₁'.1).1
        have hα₂p := (Finset.mem_inter.mp hα₂'.1).1
        have hsep := J.hp.hsep α₁ hα₁p α₂ hα₂p hne
        have hd₁ := (J.hp.hroot α₁ hα₁p x hx).2.1
        have hd₂ := (J.hp.hroot α₂ hα₂p x hx).2.1
        rw [← heq] at hd₂
        have htri : dist α₁ α₂ ≤
            dist α₁ (J.gp α₁ x) + dist (J.gp α₁ x) α₂ :=
          dist_triangle _ _ _
        rw [dist_comm α₁ (J.gp α₁ x)] at htri
        have hεpos := J.hε
        linarith
      · intro w hw
        have hwroot := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hw)
        rcases JointRootData.common_root_eq J hx
            (Polynomial.root_left_of_root_gcd hwroot)
            (Polynomial.root_right_of_root_gcd hwroot) with
          ⟨α, hα, hgp, hgq⟩
        exact ⟨α, Finset.mem_filter.mpr ⟨hα, hgp.trans hgq.symm⟩, hgp⟩
      · intro α hα
        have hα' := Finset.mem_filter.mp hα
        have hαp := (Finset.mem_inter.mp hα'.1).1
        have hαq := (Finset.mem_inter.mp hα'.1).2
        rw [rootMultiplicity_gcd (p x) (q x) hpne hqne]
        have hpm := (J.hp.hroot α hαp x hx).2.2
        have hqm := (J.hq.hroot α hαq x hx).2.2
        rw [← hα'.2] at hqm
        rw [hpm, hqm]
    _ = ∑ α ∈ commonRootFinset (p x₀) (q x₀),
        if J.gp α x = J.gq α x then min (J.ep α) (J.eq α) else 0 := by
      simpa [s] using (Finset.sum_filter
        (s := commonRootFinset (p x₀) (q x₀))
        (fun α => J.gp α x = J.gq α x)
        (fun α => min (J.ep α) (J.eq α)))

/-- Constant GCD degree forces every seated common branch to remain
    coincident throughout the joint neighbourhood. -/
theorem JointRootData.branch_eq_of_gcdNatDegree_const
    {X : Type*} [PseudoMetricSpace X]
    {p q : X → Polynomial ℂ} {x₀ : X} (J : JointRootData p q x₀)
    (hD : ∀ x y, gcdNatDegree (p x) (q x) = gcdNatDegree (p y) (q y))
    {α : ℂ} (hα : α ∈ commonRootFinset (p x₀) (q x₀)) :
    ∀ x ∈ J.U, J.gp α x = J.gq α x := by
  classical
  have hαp : α ∈ (p x₀).roots.toFinset := (Finset.mem_inter.mp hα).1
  have hαq : α ∈ (q x₀).roots.toFinset := (Finset.mem_inter.mp hα).2
  have hpos : 0 < min (J.ep α) (J.eq α) :=
    lt_min (J.hp.hepos α hαp) (J.hq.hepos α hαq)
  have hbaseEq : J.gp α x₀ = J.gq α x₀ := by
    rw [J.hp.hbase α hαp, J.hq.hbase α hαq]
  intro x hx
  by_contra hne
  let w : ℂ → ℕ := fun β =>
    if J.gp β x = J.gq β x then min (J.ep β) (J.eq β) else 0
  let w₀ : ℂ → ℕ := fun β =>
    if J.gp β x₀ = J.gq β x₀ then min (J.ep β) (J.eq β) else 0
  have hle : ∀ β ∈ commonRootFinset (p x₀) (q x₀), w β ≤ w₀ β := by
    intro β hβ
    have hβp := (Finset.mem_inter.mp hβ).1
    have hβq := (Finset.mem_inter.mp hβ).2
    have hb : J.gp β x₀ = J.gq β x₀ := by
      rw [J.hp.hbase β hβp, J.hq.hbase β hβq]
    simp only [w, w₀, hb, ite_true]
    split_ifs <;> omega
  have hlt : w α < w₀ α := by
    simp [w, w₀, hbaseEq, hne, hpos]
  have hsumlt := Finset.sum_lt_sum hle ⟨α, hα, hlt⟩
  have hxformula := JointRootData.gcdNatDegree_eq J hx
  have h0formula := JointRootData.gcdNatDegree_eq J J.hx₀
  change gcdNatDegree (p x) (q x) = ∑ β ∈ commonRootFinset (p x₀) (q x₀), w β at hxformula
  change gcdNatDegree (p x₀) (q x₀) = ∑ β ∈ commonRootFinset (p x₀) (q x₀), w₀ β at h0formula
  have hsum_eq : (∑ β ∈ commonRootFinset (p x₀) (q x₀), w β) =
      ∑ β ∈ commonRootFinset (p x₀) (q x₀), w₀ β := by
    rw [← hxformula, ← h0formula, hD x x₀]
  rw [hsum_eq] at hsumlt
  exact Nat.lt_irrefl _ hsumlt

end CollinsCAD
