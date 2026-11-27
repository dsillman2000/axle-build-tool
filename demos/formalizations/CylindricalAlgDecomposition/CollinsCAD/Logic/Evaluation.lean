import Logic.AtomPolys
import CAD.Cylinder
import CAD.Structure

namespace CollinsCAD

open FirstOrder FirstOrder.Language Polynomial MvPolynomial

/-- A bounded formula has constant truth on a CAD cell, measured at its
    sample. -/
def ConstantOnCell {n m : ℕ}
    (φ : orderedRing.BoundedFormula (Fin n) m) (C : Cell (n + m)) : Prop :=
  ∀ z ∈ C.carrier, boundedRealize φ z ↔ boundedRealize φ C.sample

/-- Quantifier-free truth is determined by the atom-polynomial signs, hence is
    constant on every invariant cell. -/
theorem boundedQF_realize_eq_sample {r k : ℕ}
    {φ : orderedRing.BoundedFormula (Fin r) k} (hφ : φ.IsQF)
    {C : Cell (r + k)}
    (hInv : SignInvariant (realAtomPolys (atomPolys φ)) C.carrier) :
    ∀ z ∈ C.carrier, boundedRealize φ z ↔ boundedRealize φ C.sample := by
  revert hInv
  induction hφ with
  | falsum =>
    intro _ z hz
    rfl
  | of_isAtomic hA =>
    intro hInv z hz
    induction hA with
    | equal t₁ t₂ =>
      have hmem : intCastMv (r + k)
          (boundedTermToMvPoly t₁ - boundedTermToMvPoly t₂) ∈
          realAtomPolys (atomPolys (t₁.bdEqual t₂)) := by
        refine mem_realAtomPolys.mpr
          ⟨boundedTermToMvPoly t₁ - boundedTermToMvPoly t₂, ?_, ?_⟩
        · exact Finset.mem_singleton_self _
        · change MvPolynomial.map (Int.castRingHom ℝ)
            (boundedTermToMvPoly t₁ - boundedTermToMvPoly t₂) = _
          simp [intCastMv]
      rcases hInv _ hmem with ⟨s, hs'⟩
      have hsign := (hs' z hz).trans (hs' C.sample C.sample_mem).symm
      rw [boundedRealize_equal_iff_sign_zero,
        boundedRealize_equal_iff_sign_zero, hsign]
    | rel R ts =>
      cases R with
      | lt =>
        have hmem : intCastMv (r + k)
            (boundedTermToMvPoly (ts 0) - boundedTermToMvPoly (ts 1)) ∈
            realAtomPolys (atomPolys (.rel orderedRingRel.lt ts)) := by
          refine mem_realAtomPolys.mpr
            ⟨boundedTermToMvPoly (ts 0) - boundedTermToMvPoly (ts 1), ?_, ?_⟩
          · exact Finset.mem_singleton_self _
          · change MvPolynomial.map (Int.castRingHom ℝ)
              (boundedTermToMvPoly (ts 0) - boundedTermToMvPoly (ts 1)) = _
            simp [intCastMv]
        rcases hInv _ hmem with ⟨s, hs'⟩
        have hsign := (hs' z hz).trans (hs' C.sample C.sample_mem).symm
        have hrel : (Relations.boundedFormula orderedRingRel.lt ts) =
            orderedRingTermLt (ts 0) (ts 1) := by
          congr 1
          funext i
          fin_cases i <;> rfl
        rw [hrel, boundedRealize_lt_iff_sign_neg_one,
          boundedRealize_lt_iff_sign_neg_one, hsign]
  | imp _ _ ih₁ ih₂ =>
    intro hInv z hz
    exact imp_congr
      (ih₁ (SignInvariant.mono hInv
        (realAtomPolys_mono (by simp [atomPolys]))) z hz)
      (ih₂ (SignInvariant.mono hInv
        (realAtomPolys_mono (by simp [atomPolys]))) z hz)

/-- Formula-level EVAL base theorem. -/
theorem qf_realize_eq_sample {n : ℕ}
    {φ : orderedRing.Formula (Fin n)} (hφ : φ.IsQF)
    {C : Cell n} (hInv : SignInvariant (realAtomPolys (atomPolys φ)) C.carrier) :
    ∀ z ∈ C.carrier, φ.Realize z ↔ φ.Realize C.sample := by
  intro z hz
  have h := boundedQF_realize_eq_sample hφ hInv z hz
  simpa only [boundedRealize_zero, Nat.add_zero] using h

/-- Quantifier-free invariance gives sample constancy on every CAD cell. -/
theorem cellConstant_of_qf_invariant {r k : ℕ} {T : CAD (r + k)}
    {φ : orderedRing.BoundedFormula (Fin r) k} (hφ : φ.IsQF)
    (hInv : CADInvariant (realAtomPolys (atomPolys φ)) T.cells) :
    ∀ C ∈ T.cells, ConstantOnCell φ C := by
  intro C hC z hz
  exact boundedQF_realize_eq_sample hφ (hInv C hC) z hz

end CollinsCAD
