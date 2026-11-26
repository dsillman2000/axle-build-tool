import Mathlib

namespace CollinsCAD

/-- The bijection $\{0,\ldots,r\}\simeq\{\ast\}\amalg\{0,\ldots,r-1\}$ sending the
    last index to the distinguished point and $\operatorname{castSucc}(j)$ to $j$. -/
def finLastIndexEquiv (r : ℕ) : Fin (r + 1) ≃ Option (Fin r) where
  toFun i := Fin.lastCases none (fun j => some j) i
  invFun o := o.elim (Fin.last r) (fun j => Fin.castSucc j)
  left_inv := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j
      simp
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some j => simp

/-- The algebra equivalence $R[X_0,\ldots,X_r]\cong R[X_0,\ldots,X_{r-1}][X]$
    viewing a multivariate polynomial as a univariate polynomial in its last variable. -/
noncomputable def finLastEquiv (R : Type*) [CommSemiring R] (r : ℕ) :
    MvPolynomial (Fin (r + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin r) R) :=
  (MvPolynomial.renameEquiv R (finLastIndexEquiv r)).trans
    (MvPolynomial.optionEquivLeft R (Fin r))

/-- The optional-variable equivalence commutes with coefficient maps. -/
private theorem optionEquivLeft_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    {σ : Type*} (f : R →+* S) (p : MvPolynomial (Option σ) R) :
    (MvPolynomial.optionEquivLeft R σ p).map (MvPolynomial.map f) =
      MvPolynomial.optionEquivLeft S σ (MvPolynomial.map f p) := by
  ext n d
  rw [Polynomial.coeff_map, MvPolynomial.optionEquivLeft_coeff_coeff,
    MvPolynomial.coeff_map, MvPolynomial.optionEquivLeft_coeff_coeff]
  simp [MvPolynomial.coeff_map]

/-- The last-variable splitting equivalence commutes with coefficient maps. -/
theorem finLastEquiv_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (r : ℕ) (p : MvPolynomial (Fin (r + 1)) R) :
    finLastEquiv S r (MvPolynomial.map f p) =
      (finLastEquiv R r p).map (MvPolynomial.map f) := by
  change MvPolynomial.optionEquivLeft S (Fin r)
      (MvPolynomial.rename (finLastIndexEquiv r) (MvPolynomial.map f p)) =
    (MvPolynomial.optionEquivLeft R (Fin r)
      (MvPolynomial.rename (finLastIndexEquiv r) p)).map (MvPolynomial.map f)
  rw [← MvPolynomial.map_rename]
  exact (optionEquivLeft_map f _).symm

/-- The inverse last-variable splitting equivalence commutes with coefficient
    maps. -/
theorem finLastEquiv_symm_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (r : ℕ) (D : Polynomial (MvPolynomial (Fin r) R)) :
    (finLastEquiv S r).symm (D.map (MvPolynomial.map f)) =
      MvPolynomial.map f ((finLastEquiv R r).symm D) := by
  apply (finLastEquiv S r).injective
  rw [AlgEquiv.apply_symm_apply, finLastEquiv_map, AlgEquiv.apply_symm_apply]

end CollinsCAD
