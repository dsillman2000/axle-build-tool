import Mathlib
import Algebra.FinLastEquiv

namespace CollinsCAD

open MvPolynomial

/-- Evaluation commutes with the last-variable equivalence:
    $\operatorname{ev}_{(a,x)}(P)=\operatorname{ev}_x\big(\operatorname{map}(\operatorname{ev}_a)(\mathrm{finLastEquiv}(P))\big)$.
    Here $(a,x)$ denotes the tuple obtained by appending $x$ to $a$. -/
theorem eval_last_comm {R : Type*} [CommSemiring R] (r : ℕ)
    (P : MvPolynomial (Fin (r + 1)) R) (a : Fin r → R) (x : R) :
    MvPolynomial.eval (Fin.snoc a x) P =
      Polynomial.eval x ((finLastEquiv R r P).map (MvPolynomial.eval a)) := by
  rw [finLastEquiv]
  change MvPolynomial.eval (Fin.snoc a x) P =
    Polynomial.eval x (Polynomial.map (MvPolynomial.eval a)
      ((MvPolynomial.optionEquivLeft R (Fin r))
        ((MvPolynomial.rename (finLastIndexEquiv r)) P)))
  rw [← MvPolynomial.optionEquivLeft_elim_eval R (Fin r) a x
    ((MvPolynomial.rename (finLastIndexEquiv r)) P)]
  rw [MvPolynomial.eval_rename]
  apply MvPolynomial.hom_eq_hom
  · ext c
    simp
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simp [finLastIndexEquiv]
    · intro j
      simp [finLastIndexEquiv]

end CollinsCAD
