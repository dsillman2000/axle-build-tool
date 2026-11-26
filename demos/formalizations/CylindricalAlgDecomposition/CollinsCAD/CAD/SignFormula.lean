import Mathlib
import CAD.AugmentedProjection
import CAD.Integrality

namespace CollinsCAD

open Polynomial MvPolynomial

/-- A polynomial sign condition. -/
structure SignCondition (r : ℕ) where
  poly : MvPolynomial (Fin r) ℝ
  sign : SignType

/-- A sign condition holds at a point. -/
def SignCondition.Holds {r : ℕ} (c : SignCondition r) (x : Fin r → ℝ) : Prop :=
  SignType.sign (MvPolynomial.eval x c.poly) = c.sign

/-- A finite conjunction of polynomial sign conditions. -/
structure SignFormula (r : ℕ) where
  conditions : Finset (SignCondition r)

/-- A sign formula holds at a point. -/
def SignFormula.Holds {r : ℕ} (F : SignFormula r) (x : Fin r → ℝ) : Prop :=
  ∀ c ∈ F.conditions, c.Holds x

/-- Polynomial support of a sign formula. -/
noncomputable def SignFormula.polys {r : ℕ} (F : SignFormula r) : Finset (MvPolynomial (Fin r) ℝ) :=
  F.conditions.image SignCondition.poly

/-- Integrality of every condition gives integrality of the formula support. -/
theorem SignFormula.isIntPoly_of_mem_polys {r : ℕ} {F : SignFormula r}
    (hF : ∀ c ∈ F.conditions, IsIntPoly c.poly) {Q : MvPolynomial (Fin r) ℝ}
    (hQ : Q ∈ F.polys) : IsIntPoly Q := by
  rcases Finset.mem_image.mp hQ with ⟨c, hc, rfl⟩
  exact hF c hc

/-- The sign formula recording all signs at a sample point. -/
noncomputable def signFormulaOfSample {r : ℕ}
    (B : Finset (MvPolynomial (Fin r) ℝ)) (x : Fin r → ℝ) : SignFormula r := by
  classical
  exact ⟨B.image fun P => ⟨P, SignType.sign (MvPolynomial.eval x P)⟩⟩

/-- The sample sign formula records exactly the sign vector at `B`. -/
@[simp] theorem signFormulaOfSample_holds {r : ℕ}
    (B : Finset (MvPolynomial (Fin r) ℝ)) (x y : Fin r → ℝ) :
    (signFormulaOfSample B x).Holds y ↔
      ∀ P ∈ B, SignType.sign (MvPolynomial.eval y P) =
        SignType.sign (MvPolynomial.eval x P) := by
  classical
  constructor
  · intro h P hP
    have hc : (⟨P, SignType.sign (MvPolynomial.eval x P)⟩ : SignCondition r) ∈
        (signFormulaOfSample B x).conditions := by
      simp [signFormulaOfSample, hP]
    exact h _ hc
  · intro h c hc
    rcases Finset.mem_image.mp hc with ⟨P, hP, rfl⟩
    exact h P hP

/-- Embed a lower-dimensional polynomial as constant in the last variable. -/
noncomputable def prefixPoly {r : ℕ} (P : MvPolynomial (Fin r) ℝ) :
    MvPolynomial (Fin (r + 1)) ℝ :=
  (finLastEquiv ℝ r).symm (Polynomial.C P)

/-- Prefixing preserves integer coefficients. -/
theorem IsIntPoly.prefix {P : MvPolynomial (Fin r) ℝ}
    (hP : IsIntPoly P) : IsIntPoly (prefixPoly P) := by
  rcases hP with ⟨P₀, rfl⟩
  refine ⟨(finLastEquiv ℤ r).symm (Polynomial.C P₀), ?_⟩
  simpa [prefixPoly, intCastMv, Polynomial.map_C] using
    finLastEquiv_symm_map (Int.castRingHom ℝ) r (Polynomial.C P₀)

@[simp] theorem eval_prefixPoly {r : ℕ} (P : MvPolynomial (Fin r) ℝ)
    (a : Fin r → ℝ) (x : ℝ) :
    MvPolynomial.eval (Fin.snoc a x) (prefixPoly P) = MvPolynomial.eval a P := by
  change MvPolynomial.eval (Fin.snoc a x)
    ((finLastEquiv ℝ r).symm (Polynomial.C P)) = _
  rw [← fiberPoly_eval, fiberPoly_finLastEquiv_symm]
  simp

/-- Prefix a sign formula to the next dimension. -/
noncomputable def SignFormula.prefix {r : ℕ} (F : SignFormula r) :
    SignFormula (r + 1) := by
  classical
  exact ⟨F.conditions.image fun c => ⟨prefixPoly c.poly, c.sign⟩⟩

/-- Prefixing preserves truth on the first `r` coordinates. -/
theorem SignFormula.prefix_holds {r : ℕ} (F : SignFormula r)
    (z : Fin (r + 1) → ℝ) :
    F.prefix.Holds z ↔ F.Holds (fun i => z (Fin.castSucc i)) := by
  classical
  have hzsnoc : z = Fin.snoc (Fin.init z) (z (Fin.last r)) :=
    (Fin.snoc_init_self z).symm
  have hinit : Fin.init z = (fun i : Fin r => z (Fin.castSucc i)) := by
    funext i
    simp [Fin.init]
  constructor
  · intro h c hc
    have hc' : (⟨prefixPoly c.poly, c.sign⟩ : SignCondition (r + 1)) ∈
        F.prefix.conditions :=
      Finset.mem_image.mpr ⟨c, hc, rfl⟩
    have hz := h _ hc'
    change SignType.sign (MvPolynomial.eval z (prefixPoly c.poly)) = c.sign at hz
    rw [hzsnoc, eval_prefixPoly] at hz
    simpa only [SignCondition.Holds, ← hinit] using hz
  · intro h c hc
    rcases Finset.mem_image.mp hc with ⟨d, hd, rfl⟩
    have hd' := h d hd
    change SignType.sign (MvPolynomial.eval z (prefixPoly d.poly)) = d.sign
    rw [hzsnoc, eval_prefixPoly]
    simpa only [SignCondition.Holds, ← hinit] using hd'

/-- Union of two sign formulas. -/
noncomputable def SignFormula.union {r : ℕ} (F G : SignFormula r) : SignFormula r := by
  classical
  exact ⟨F.conditions ∪ G.conditions⟩

/-- Truth of a union is the conjunction of its two truth values. -/
@[simp] theorem SignFormula.union_holds {r : ℕ} (F G : SignFormula r)
    (x : Fin r → ℝ) : (F.union G).Holds x ↔ F.Holds x ∧ G.Holds x := by
  classical
  simp [SignFormula.union, SignFormula.Holds, or_imp]
  aesop

/-- Polynomial support of a union. -/
@[simp] theorem SignFormula.polys_union {r : ℕ} (F G : SignFormula r) :
    (F.union G).polys = F.polys ∪ G.polys := by
  classical
  simp [SignFormula.union, SignFormula.polys, Finset.image_union]

/-- Polynomial support of a prefix. -/
@[simp] theorem SignFormula.polys_prefix {r : ℕ} (F : SignFormula r) :
    F.prefix.polys = F.polys.image prefixPoly := by
  classical
  simp [SignFormula.prefix, SignFormula.polys, Finset.image_image]
  rfl

/-- Polynomial support of a sample sign formula. -/
@[simp] theorem SignFormula.polys_signFormulaOfSample {r : ℕ}
    (B : Finset (MvPolynomial (Fin r) ℝ)) (x : Fin r → ℝ) :
    (signFormulaOfSample B x).polys = B := by
  classical
  simp [signFormulaOfSample, SignFormula.polys, Finset.image_image]
  change B.image (fun P => P) = B
  exact Finset.image_id

/-- Prefix truth can be stated using `Fin.init`. -/
theorem SignFormula.prefix_holds_init {r : ℕ} (F : SignFormula r)
    (z : Fin (r + 1) → ℝ) : F.prefix.Holds z ↔ F.Holds (Fin.init z) := by
  have hinit : Fin.init z = (fun i : Fin r => z (Fin.castSucc i)) := by
    funext i
    simp [Fin.init]
  rw [SignFormula.prefix_holds F, hinit]

/-- Finite polynomial support envelope for DEFINE. -/
noncomputable def definePolys : (r : ℕ) →
    Finset (MvPolynomial (Fin r) ℝ) → Finset (MvPolynomial (Fin r) ℝ)
  | 0, _ => ∅
  | r + 1, A =>
      (definePolys r (augProj A)).image prefixPoly ∪ augPolySet A

@[simp] theorem mem_definePolys_succ {r : ℕ}
    {A : Finset (MvPolynomial (Fin (r + 1)) ℝ)}
    {Q : MvPolynomial (Fin (r + 1)) ℝ} :
    Q ∈ definePolys (r + 1) A ↔
      (∃ P ∈ definePolys r (augProj A), Q = prefixPoly P) ∨ Q ∈ augPolySet A := by
  simp [definePolys, Finset.mem_union, Finset.mem_image]
  aesop

/-- The DEFINE support envelope preserves integer coefficients. -/
theorem isIntPoly_of_mem_definePolys (r : ℕ) :
    ∀ (A : Finset (MvPolynomial (Fin r) ℝ)), IsIntPolyFamily A →
      ∀ Q ∈ definePolys r A, IsIntPoly Q := by
  induction r with
  | zero =>
    intro A hA Q hQ
    simp [definePolys] at hQ
  | succ r ih =>
    intro A hA Q hQ
    rcases mem_definePolys_succ.mp hQ with ⟨P, hP, rfl⟩ | hQ
    · exact IsIntPoly.prefix (ih (augProj A)
        (fun R hR => isIntPoly_of_mem_augProj hA hR) P hP)
    · exact isIntPoly_of_mem_augPolySet hA hQ

end CollinsCAD
