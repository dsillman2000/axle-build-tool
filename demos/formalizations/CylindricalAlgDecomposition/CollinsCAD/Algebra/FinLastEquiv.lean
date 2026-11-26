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

end CollinsCAD
