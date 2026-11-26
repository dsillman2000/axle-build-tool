import Mathlib
import CAD.CylinderPartition
import CAD.AugmentedProjection
import CAD.LiftRootSeparation
import Analysis.ThomFamily

namespace CollinsCAD

open Polynomial MvPolynomial

variable {r : ℕ}

/-- Nonzero fibres give a nonzero univariate fibre family. -/
theorem fiberFamily_ne_zero (L : Cylinder r)
    (hne : ∀ Q ∈ L.family, ∀ a ∈ L.parent.carrier, fiberPoly r Q a ≠ 0)
    (a : Fin r → ℝ) (ha : a ∈ L.parent.carrier) :
    ∀ q ∈ fiberFamily L.family a, q ≠ 0 := by
  intro q hq
  rcases mem_fiberFamily.mp hq with ⟨Q, hQ, rfl⟩
  exact hne Q hQ a ha

/-- Equal signs on the augmented family give equal derivative signs on the
    corresponding univariate fibre family. -/
theorem sameDerivativeSigns_fiberFamily_of_sign_eq (L : Cylinder r)
    (hderiv : ∀ Q ∈ L.family, ∀ D ∈ derivativeTower (finLastEquiv ℝ r Q),
      (finLastEquiv ℝ r).symm D ∈ L.family ∨
        ∀ a ∈ L.parent.carrier, fiberPoly r ((finLastEquiv ℝ r).symm D) a = 0)
    (a : Fin r → ℝ) (ha : a ∈ L.parent.carrier) {x y : ℝ}
    (hsign : ∀ Q ∈ L.family,
      SignType.sign (Polynomial.eval x (fiberPoly r Q a)) =
        SignType.sign (Polynomial.eval y (fiberPoly r Q a))) :
    SameDerivativeSigns (fiberFamily L.family a) x y := by
  intro q hq k hk
  rcases mem_fiberFamily.mp hq with ⟨Q, hQ, rfl⟩
  have hkfull : k ≤ (finLastEquiv ℝ r Q).natDegree := by
    exact hk.trans (Polynomial.natDegree_map_le
      (p := finLastEquiv ℝ r Q) (f := MvPolynomial.eval a))
  by_cases hDzero : derivativeIter k (finLastEquiv ℝ r Q) = 0
  · have hfib : Polynomial.derivative^[k] (fiberPoly r Q a) = 0 := by
      rw [← fiberPoly_derivative_iterate, hDzero]
      simp [fiberPoly]
    simp [derivativeSignVector, iteratedDerivative, hfib]
  · have hDtower : derivativeIter k (finLastEquiv ℝ r Q) ∈
        derivativeTower (finLastEquiv ℝ r Q) :=
      mem_derivativeTower.mpr ⟨k, hkfull, rfl, hDzero⟩
    rcases hderiv Q hQ _ hDtower with hret | hzero
    · change SignType.sign (Polynomial.eval x
        (Polynomial.derivative^[k] (fiberPoly r Q a))) =
        SignType.sign (Polynomial.eval y
          (Polynomial.derivative^[k] (fiberPoly r Q a)))
      rw [← fiberPoly_derivative_iterate]
      exact hsign _ hret
    · have hfib : Polynomial.derivative^[k] (fiberPoly r Q a) = 0 := by
        rw [← fiberPoly_derivative_iterate, hzero a ha]
      simp [derivativeSignVector, iteratedDerivative, hfib]

/-- Fibre membership is unique in a certified cylinder partition. -/
theorem IsCylinderPartition.fiber_unique (L : Cylinder r)
    (hL : IsCylinderPartition L) {a : Fin r → ℝ} (ha : a ∈ L.parent.carrier)
    (x : ℝ) : ∃ c ∈ L.children, Fin.snoc a x ∈ c.carrier ∧
      ∀ d ∈ L.children, Fin.snoc a x ∈ d.carrier → d = c := by
  rcases hL.1 a ha x with ⟨c, hc, hxc⟩
  refine ⟨c, hc, hxc, ?_⟩
  intro d hd hxd
  by_contra hne
  exact (Set.disjoint_left.mp (hL.2.2.1 c hc d hd (Ne.symm hne))) hxc hxd

/-- Two points in the same lifted child have equal fibre signs. -/
theorem Cylinder.sign_fiber_eq_of_mem (L : Cylinder r) {d : Cell (r + 1)}
    (hd : d ∈ L.children) {Q : MvPolynomial (Fin (r + 1)) ℝ} (hQ : Q ∈ L.family)
    {z w : Fin (r + 1) → ℝ} (hz : z ∈ d.carrier) (hw : w ∈ d.carrier) :
    SignType.sign (Polynomial.eval (z (Fin.last r))
      (fiberPoly r Q (Fin.init z))) =
    SignType.sign (Polynomial.eval (w (Fin.last r))
      (fiberPoly r Q (Fin.init w))) := by
  rcases L.invariant d hd Q hQ with ⟨s, hs⟩
  simpa only [fiberPoly_eval, Fin.snoc_init_self] using
    (hs z hz).trans (hs w hw).symm

/-- Two points over the same base point in one lifted child have equal
    fibre signs. -/
theorem Cylinder.sign_fiber_eq_of_snoc_mem (L : Cylinder r) {d : Cell (r + 1)}
    (hd : d ∈ L.children) {Q : MvPolynomial (Fin (r + 1)) ℝ} (hQ : Q ∈ L.family)
    {a : Fin r → ℝ} {x y : ℝ}
    (hx : Fin.snoc a x ∈ d.carrier) (hy : Fin.snoc a y ∈ d.carrier) :
    SignType.sign (Polynomial.eval x (fiberPoly r Q a)) =
      SignType.sign (Polynomial.eval y (fiberPoly r Q a)) := by
  rcases L.invariant d hd Q hQ with ⟨s, hs⟩
  simpa only [fiberPoly_eval] using (hs _ hx).trans (hs _ hy).symm

/-- Fibre signs agree at two points of the same lifted child, even when their
    base coordinates differ. -/
theorem Cylinder.sign_fiber_eq_of_snoc_mem_general (L : Cylinder r) {d : Cell (r + 1)}
    (hd : d ∈ L.children) {Q : MvPolynomial (Fin (r + 1)) ℝ} (hQ : Q ∈ L.family)
    {a₁ a₂ : Fin r → ℝ} {x₁ x₂ : ℝ}
    (hx : Fin.snoc a₁ x₁ ∈ d.carrier) (hy : Fin.snoc a₂ x₂ ∈ d.carrier) :
    SignType.sign (Polynomial.eval x₁ (fiberPoly r Q a₁)) =
      SignType.sign (Polynomial.eval x₂ (fiberPoly r Q a₂)) := by
  rcases L.invariant d hd Q hQ with ⟨s, hs⟩
  simpa only [fiberPoly_eval] using (hs _ hx).trans (hs _ hy).symm

/-- Equal augmented-family signs determine a unique lifted child over a fixed
    base point. -/
theorem Cylinder.child_eq_of_signVector_eq (L : Cylinder r)
    (hL : IsCylinderPartition L)
    (hne : ∀ Q ∈ L.family, ∀ a ∈ L.parent.carrier, fiberPoly r Q a ≠ 0)
    (hderiv : ∀ Q ∈ L.family, ∀ D ∈ derivativeTower (finLastEquiv ℝ r Q),
      (finLastEquiv ℝ r).symm D ∈ L.family ∨
        ∀ a ∈ L.parent.carrier, fiberPoly r ((finLastEquiv ℝ r).symm D) a = 0)
    {c d : Cell (r + 1)} (hc : c ∈ L.children) (hd : d ∈ L.children)
    {a : Fin r → ℝ} (ha : a ∈ L.parent.carrier) {x y : ℝ}
    (hx : Fin.snoc a x ∈ c.carrier) (hy : Fin.snoc a y ∈ d.carrier)
    (hsign : ∀ Q ∈ L.family,
      SignType.sign (Polynomial.eval x (fiberPoly r Q a)) =
        SignType.sign (Polynomial.eval y (fiberPoly r Q a))) : c = d := by
  by_cases hcd : c = d
  · exact hcd
  · have hxy : x = y := by
      apply eq_of_rootSeparatedByFamily_of_sameDerivativeSigns
        (fiberFamily_ne_zero L hne a ha)
      · exact LiftShape.rootSeparated_of_ne L (L.children_shape c hc)
          (L.children_shape d hd) hcd ha hx hy
      · exact sameDerivativeSigns_fiberFamily_of_sign_eq L hderiv a ha hsign
    rcases IsCylinderPartition.fiber_unique L hL ha x with ⟨c₀, hc₀, hxc₀, huniq⟩
    exact (huniq c hc (by simpa [hxy] using hx)).trans
      (huniq d hd (by simpa [hxy] using hy)).symm

end CollinsCAD
