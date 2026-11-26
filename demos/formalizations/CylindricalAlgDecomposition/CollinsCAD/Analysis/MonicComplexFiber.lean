import Mathlib

namespace CollinsCAD

open Polynomial

/-- The monic complex polynomial obtained by scaling a real polynomial by the
    inverse of its complexified leading coefficient. -/
noncomputable def monicComplexFiber {X : Type*} (q : X → Polynomial ℝ) (d : ℕ)
    (x : X) : Polynomial ℂ :=
  (q x).map (algebraMap ℝ ℂ) *
    Polynomial.C ((algebraMap ℝ ℂ ((q x).coeff d))⁻¹)

/-- Coefficients of the monic complex normalization. -/
theorem coeff_monicComplexFiber {X : Type*} (q : X → Polynomial ℝ) (d : ℕ)
    (x : X) (k : ℕ) :
    (monicComplexFiber q d x).coeff k =
      (algebraMap ℝ ℂ) ((q x).coeff k) *
        (algebraMap ℝ ℂ ((q x).coeff d))⁻¹ := by
  simp [monicComplexFiber, Polynomial.coeff_mul_C, Polynomial.coeff_map]

/-- Coefficient continuity of the monic complex normalization. -/
theorem continuous_monicComplexFiber_coeff {X : Type*} [TopologicalSpace X]
    (q : X → Polynomial ℝ) (hcoeff : ∀ k : ℕ, Continuous (fun x => (q x).coeff k))
    (d : ℕ) (hlc : ∀ x, (q x).coeff d ≠ 0) (k : ℕ) :
    Continuous (fun x => (monicComplexFiber q d x).coeff k) := by
  have hlead : Continuous (fun x => (algebraMap ℝ ℂ) ((q x).coeff d)) :=
    Complex.continuous_ofReal.comp (hcoeff d)
  have hinv : Continuous (fun x => (algebraMap ℝ ℂ ((q x).coeff d))⁻¹) :=
    hlead.inv₀ (fun x => Complex.ofReal_ne_zero.mpr (hlc x))
  have hcoeffk : Continuous (fun x => (algebraMap ℝ ℂ) ((q x).coeff k)) :=
    Complex.continuous_ofReal.comp (hcoeff k)
  rw [show (fun x => (monicComplexFiber q d x).coeff k) =
      (fun x => (algebraMap ℝ ℂ ((q x).coeff k)) *
        (algebraMap ℝ ℂ ((q x).coeff d))⁻¹) by
    funext x
    exact coeff_monicComplexFiber q d x k]
  exact hcoeffk.mul hinv

/-- The normalization preserves the prescribed positive degree. -/
theorem natDegree_monicComplexFiber {X : Type*} (q : X → Polynomial ℝ) (d : ℕ)
    (hdeg : ∀ x, (q x).natDegree = d) (hlc : ∀ x, (q x).coeff d ≠ 0) (x : X) :
    (monicComplexFiber q d x).natDegree = d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · dsimp [monicComplexFiber]
    calc
      ((q x).map (algebraMap ℝ ℂ) *
          Polynomial.C ((algebraMap ℝ ℂ ((q x).coeff d))⁻¹)).natDegree
          ≤ ((q x).map (algebraMap ℝ ℂ)).natDegree := Polynomial.natDegree_mul_C_le _ _
      _ = (q x).natDegree :=
        Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective (q x)
      _ = d := hdeg x
  · have hc : (algebraMap ℝ ℂ ((q x).coeff d)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hlc x)
    dsimp [monicComplexFiber]
    simpa [Polynomial.coeff_mul_C] using mul_ne_zero hc (inv_ne_zero hc)

/-- The normalization is monic. -/
theorem monic_monicComplexFiber {X : Type*} (q : X → Polynomial ℝ) (d : ℕ)
    (hdeg : ∀ x, (q x).natDegree = d) (hlc : ∀ x, (q x).coeff d ≠ 0) (x : X) :
    (monicComplexFiber q d x).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one d
    (le_of_eq (natDegree_monicComplexFiber q d hdeg hlc x))
  have hc : (algebraMap ℝ ℂ ((q x).coeff d)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hlc x)
  dsimp [monicComplexFiber]
  simpa [Polynomial.coeff_mul_C] using mul_inv_cancel₀ hc

/-- Scaling by a nonzero constant does not change roots. -/
theorem roots_monicComplexFiber {X : Type*} (q : X → Polynomial ℝ) (d : ℕ)
    (hlc : ∀ x, (q x).coeff d ≠ 0) (x : X) :
    (monicComplexFiber q d x).roots = ((q x).map (algebraMap ℝ ℂ)).roots := by
  dsimp [monicComplexFiber]
  rw [mul_comm, Polynomial.roots_C_mul]
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (hlc x))

/-- The normalized polynomial has real coefficients. -/
theorem im_coeff_monicComplexFiber {X : Type*} (q : X → Polynomial ℝ) (d : ℕ)
    (x : X) (k : ℕ) : ((monicComplexFiber q d x).coeff k).im = 0 := by
  rw [coeff_monicComplexFiber]
  simp

end CollinsCAD
