import Mathlib

namespace CollinsCAD

/-- The $k$-fold reductum $\operatorname{red}_k(p)$ of a polynomial $p$, obtained by
    deleting the leading term $k$ times. -/
noncomputable def reductum {R : Type*} [Semiring R] : ℕ → Polynomial R → Polynomial R
  | 0, p => p
  | k + 1, p => (reductum k p).eraseLead

/-- The zeroth reductum leaves the polynomial unchanged: $\operatorname{red}_0(p)=p$. -/
@[simp] theorem reductum_zero {R : Type*} [Semiring R] (p : Polynomial R) :
    reductum 0 p = p := rfl

/-- The reductum satisfies $\operatorname{red}_{k+1}(p)=\operatorname{eraseLead}(\operatorname{red}_k(p))$. -/
@[simp] theorem reductum_succ {R : Type*} [Semiring R] (k : ℕ) (p : Polynomial R) :
    reductum (k + 1) p = (reductum k p).eraseLead := by
  simp [reductum]

/-- Reducta of the zero polynomial vanish: $\operatorname{red}_k(0)=0$. -/
@[simp] theorem reductum_zero_poly {R : Type*} [Semiring R] (k : ℕ) :
    reductum k (0 : Polynomial R) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [reductum, ih]

end CollinsCAD
