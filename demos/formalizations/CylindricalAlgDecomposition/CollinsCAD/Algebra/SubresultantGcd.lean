import Mathlib
import Algebra.SubresultantKernel

namespace CollinsCAD

open Polynomial

/-- Reconstruct a polynomial of degree $<d$ from its first $d$ coefficients. -/
noncomputable def polyOfVector {K : Type*} [Field K] (d : ℕ) (c : Fin d → K) : Polynomial K :=
  ((Polynomial.degreeLTEquiv K d).symm c : Polynomial.degreeLT K d)

/-- The coefficients of `polyOfVector` are the entries of the vector, with zeros beyond $d$. -/
theorem coeff_polyOfVector {K : Type*} [Field K] (d : ℕ) (c : Fin d → K) (n : ℕ) :
    (polyOfVector d c).coeff n = if h : n < d then c ⟨n, h⟩ else 0 := by
  by_cases h : n < d
  · have hc := congrFun (show (Polynomial.degreeLTEquiv K d)
        ((Polynomial.degreeLTEquiv K d).symm c) = c by simp) (⟨n, h⟩ : Fin d)
    simpa [polyOfVector, Polynomial.degreeLTEquiv, h] using hc
  · have hd : (polyOfVector d c) ∈ Polynomial.degreeLT K d :=
      ((Polynomial.degreeLTEquiv K d).symm c).property
    have hdeg : (polyOfVector d c).degree < (n : WithBot ℕ) :=
      (Polynomial.mem_degreeLT.mp hd).trans_le (by exact_mod_cast (Nat.le_of_not_gt h))
    simp [h, Polynomial.coeff_eq_zero_of_degree_lt hdeg]

end CollinsCAD
