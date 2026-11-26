import Mathlib

namespace CollinsCAD

open Polynomial

/-- In characteristic zero, a nonconstant polynomial has nonzero derivative
    leading coefficient. -/
theorem leadingCoeff_derivative_ne_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (B : Polynomial R) (hdeg : 0 < B.natDegree) : B.derivative.leadingCoeff ≠ 0 := by
  have hB0 : B ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hdeg
  rw [Polynomial.leadingCoeff_derivative]
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hB0)
    (Nat.cast_ne_zero.mpr (by omega))

/-- Evaluation preserves nonvanishing of the derivative leading coefficient. -/
theorem derivative_leadingCoeff_eval_ne_zero {r : ℕ}
    (B : Polynomial (MvPolynomial (Fin r) ℝ)) (a : Fin r → ℝ)
    (hdeg : 0 < B.natDegree)
    (hlc : MvPolynomial.eval a B.leadingCoeff ≠ 0) :
    MvPolynomial.eval a B.derivative.leadingCoeff ≠ 0 := by
  have heq : MvPolynomial.eval a B.derivative.leadingCoeff =
      MvPolynomial.eval a B.leadingCoeff * (B.natDegree : ℝ) := by
    rw [Polynomial.leadingCoeff_derivative, map_mul, map_natCast]
  rw [heq]
  exact mul_ne_zero hlc (Nat.cast_ne_zero.mpr (by omega))

end CollinsCAD
