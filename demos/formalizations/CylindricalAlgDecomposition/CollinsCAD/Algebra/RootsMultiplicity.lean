import Mathlib

namespace CollinsCAD

open Polynomial

/-- For a root $\alpha$ of $A$, its multiplicity in $A'$ is one less than its multiplicity in $A$. -/
theorem roots_multiplicity_derivative {K : Type*} [Field K] [CharZero K]
    (A : Polynomial K) (α : K) (hα : A.IsRoot α) :
    rootMultiplicity α A.derivative = rootMultiplicity α A - 1 :=
  Polynomial.derivative_rootMultiplicity_of_root hα

end CollinsCAD
