import Mathlib
import CAD.Decomp
import CAD.Define
import Logic.Elim

/-!
# Trivial CAD test 1: one-dimensional linear polynomial $x_0 - 1$

This file pins down the explicit algebraic, geometric, and logical CAD data for
the univariate linear polynomial $P(x_0) = x_0 - 1 \in \mathbb{R}[x_0]$:
last-variable view, reducta, leading-coefficient projection, the explicit
three-cell decomposition $(-\infty, 1) \cup \{1\} \cup (1, \infty)$ with sample
points $0, 1, 2$, sign invariance on each cell, and first-order quantifier
elimination for $\exists x,\, x - 1 = 0$.
-/

open scoped FirstOrder.Language

namespace CollinsCAD

open Polynomial MvPolynomial FirstOrder FirstOrder.Language

/-- Last-variable splitting sends `X (Fin.last r)` to the univariate variable
    `Polynomial.X`. -/
@[simp] theorem finLastEquiv_X_last (R : Type*) [CommSemiring R] (r : ℕ) :
    finLastEquiv R r (MvPolynomial.X (Fin.last r)) = Polynomial.X := by
  simp [finLastEquiv, finLastIndexEquiv]

/-- Last-variable splitting sends an earlier variable `X (Fin.castSucc i)` to
    the constant polynomial `Polynomial.C (X i)`. -/
@[simp] theorem finLastEquiv_X_castSucc (R : Type*) [CommSemiring R] (r : ℕ)
    (i : Fin r) :
    finLastEquiv R r (MvPolynomial.X (Fin.castSucc i)) =
      Polynomial.C (MvPolynomial.X i) := by
  simp [finLastEquiv, finLastIndexEquiv]

/-- The test polynomial $P(x_0) = x_0 - 1$ in dimension $r = 1$. -/
noncomputable def linear1DPoly : MvPolynomial (Fin 1) ℝ :=
  MvPolynomial.X 0 - 1

/-- Under `finLastEquiv`, $x_0 - 1$ becomes $X - 1 \in \mathbb{R}[][X]$. -/
theorem finLastEquiv_linear1DPoly :
    finLastEquiv ℝ 0 linear1DPoly = Polynomial.X - 1 := by
  change finLastEquiv ℝ 0 (MvPolynomial.X (Fin.last 0) - 1) = Polynomial.X - 1
  rw [map_sub, map_one, finLastEquiv_X_last]

/-- Evaluating the fibre polynomial of $x_0 - 1$ over the unique 0D point gives
    $X - 1 \in \mathbb{R}[X]$. -/
theorem fiberPoly_linear1DPoly (a : Fin 0 → ℝ) :
    fiberPoly 0 linear1DPoly a = Polynomial.X - 1 := by
  simp [fiberPoly, finLastEquiv_linear1DPoly]

/-- The zeroth reductum of $X - 1$ is $X - 1$. -/
theorem reductum_zero_linear1DPoly :
    reductum 0 (finLastEquiv ℝ 0 linear1DPoly) = Polynomial.X - 1 := by
  rw [reductum_zero, finLastEquiv_linear1DPoly]

/-- In a commutative ring, `eraseLead p` is obtained by subtracting the leading
    monomial `C p.leadingCoeff * X ^ p.natDegree`. -/
theorem eraseLead_eq_sub_leadingTerm {R : Type*} [CommRing R] (p : Polynomial R) :
    p.eraseLead = p - Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree := by
  rw [eq_sub_iff_add_eq, Polynomial.C_mul_X_pow_eq_monomial]
  exact Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff p

/-- The first reductum of $X - 1$ is the constant polynomial $-1$. -/
theorem reductum_one_linear1DPoly :
    reductum 1 (finLastEquiv ℝ 0 linear1DPoly) = -1 := by
  rw [reductum_succ, reductum_zero_linear1DPoly, eraseLead_eq_sub_leadingTerm]
  have h1 : (Polynomial.X - 1 : Polynomial (MvPolynomial (Fin 0) ℝ)) =
      Polynomial.X - Polynomial.C 1 := by simp
  have hdeg : (Polynomial.X - 1 : Polynomial (MvPolynomial (Fin 0) ℝ)).natDegree = 1 := by
    rw [h1, Polynomial.natDegree_X_sub_C]
  have hlc : (Polynomial.X - 1 : Polynomial (MvPolynomial (Fin 0) ℝ)).leadingCoeff = 1 := by
    rw [h1, Polynomial.leadingCoeff_X_sub_C]
  rw [hdeg, hlc]
  simp

/-- The second reductum of $X - 1$ vanishes. -/
theorem reductum_two_linear1DPoly :
    reductum 2 (finLastEquiv ℝ 0 linear1DPoly) = 0 := by
  rw [reductum_succ, reductum_one_linear1DPoly]
  have hneg : (-1 : Polynomial (MvPolynomial (Fin 0) ℝ)) = Polynomial.C (-1) := by
    simp
  rw [hneg, Polynomial.eraseLead_C]

/-- Both $1$ and $-1$ appear in the leading-coefficient projection `projL` of
    $\{x_0 - 1\}$. -/
theorem one_mem_collinsProj_linear1DPoly :
    (1 : MvPolynomial (Fin 0) ℝ) ∈ collinsProj {linear1DPoly} := by
  have hred0 : reductum 0 (finLastEquiv ℝ 0 linear1DPoly) ≠ 0 := by
    rw [reductum_zero_linear1DPoly]
    exact Polynomial.X_sub_C_ne_zero 1
  have hmem : reductum 0 (finLastEquiv ℝ 0 linear1DPoly) ∈
      reductaSet {linear1DPoly} :=
    reductum_mem_reductaSet (by simp) hred0
  have hlc : (reductum 0 (finLastEquiv ℝ 0 linear1DPoly)).leadingCoeff = 1 := by
    rw [reductum_zero_linear1DPoly]
    have h1 : (Polynomial.X - 1 : Polynomial (MvPolynomial (Fin 0) ℝ)) =
        Polynomial.X - Polynomial.C 1 := by simp
    rw [h1, Polynomial.leadingCoeff_X_sub_C]
  rw [← hlc]
  exact leadingCoeff_mem_collinsProj hmem

/-- The root family over `baseCell0` consisting of the single root $x_0 = 1$. -/
noncomputable def linear1DRoots : RootFamily baseCell0.carrier where
  k := 1
  f := fun _ _ => 1
  continuous := fun _ => continuousOn_const
  ordered := by
    intro i j _ _ hij
    omega

/-- The explicit list of three 1D cells for $x_0 - 1$:
    $(-\infty, 1)$, $\{1\}$, and $(1, \infty)$. -/
theorem liftCells_linear1DRoots :
    liftCells baseCell0 linear1DRoots =
      [Cell.lower baseCell0 (fun _ => 1) continuousOn_const,
       Cell.graph baseCell0 (fun _ => 1) continuousOn_const,
       Cell.upper baseCell0 (fun _ => 1) continuousOn_const] := by
  unfold liftCells linear1DRoots
  simp [liftCellsAux_one]

/-- The three lifted cells of `linear1DRoots` have sample points $0$, $1$,
    and $2$ respectively. -/
theorem linear1D_samples :
    (Cell.lower baseCell0 (fun _ => 1) continuousOn_const).sample 0 = 0 ∧
    (Cell.graph baseCell0 (fun _ => 1) continuousOn_const).sample 0 = 1 ∧
    (Cell.upper baseCell0 (fun _ => 1) continuousOn_const).sample 0 = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · change @Fin.snoc 0 (fun _ => ℝ) baseCell0.sample ((1 : ℝ) - 1) (Fin.last 0) = 0
    rw [Fin.snoc_last]
    ring
  · change @Fin.snoc 0 (fun _ => ℝ) baseCell0.sample (1 : ℝ) (Fin.last 0) = 1
    rw [Fin.snoc_last]
  · change @Fin.snoc 0 (fun _ => ℝ) baseCell0.sample ((1 : ℝ) + 1) (Fin.last 0) = 2
    rw [Fin.snoc_last]
    ring

/-- The polynomial $x_0 - 1$ is sign-invariant on each of the three cells of
    `liftCells baseCell0 linear1DRoots`. -/
theorem linear1D_cells_signInvariant :
    ∀ c ∈ liftCells baseCell0 linear1DRoots,
      SignInvariant {linear1DPoly} c.carrier := by
  rw [liftCells_linear1DRoots]
  intro c hc P hP
  have hPeq : P = linear1DPoly := Finset.mem_singleton.mp hP
  subst P
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · refine ⟨-1, ?_⟩
    intro z hz
    have hlt : z 0 < 1 := (Cell.mem_lower.mp hz).2
    have heval : MvPolynomial.eval z linear1DPoly = z 0 - 1 := by
      simp [linear1DPoly]
    rw [heval, sign_eq_neg_one_iff]
    linarith
  · refine ⟨0, ?_⟩
    intro z hz
    have heq : z 0 = 1 := (Cell.mem_graph.mp hz).2
    have heval : MvPolynomial.eval z linear1DPoly = z 0 - 1 := by
      simp [linear1DPoly]
    rw [heval, heq, sub_self, sign_zero]
  · refine ⟨1, ?_⟩
    intro z hz
    have hgt : 1 < z 0 := (Cell.mem_upper.mp hz).2
    have heval : MvPolynomial.eval z linear1DPoly = z 0 - 1 := by
      simp [linear1DPoly]
    rw [heval, sign_eq_one_iff]
    linarith

/-- The canonical 1D cylinder over `baseCell0` for $\{x_0 - 1\}$. -/
noncomputable def linear1DCylinder : Cylinder 0 :=
  Cylinder.canonical baseCell0 linear1DRoots {linear1DPoly}
    linear1D_cells_signInvariant
    (by
      intro i a _
      refine ⟨linear1DPoly, by simp, ?_⟩
      rw [fiberPoly_linear1DPoly]
      change Polynomial.eval (1 : ℝ) (Polynomial.X - 1) = 0
      simp)

/-- The canonical cylinder for $x_0 - 1$ is a valid cylinder partition with
    exactly $3$ child cells. -/
theorem linear1DCylinder_isPartition :
    IsCylinderPartition linear1DCylinder ∧
    linear1DCylinder.children.length = 3 :=
  ⟨IsCylinderPartition.canonical _ _ _ _ _,
   linear1DCylinder.children_length⟩

/-- The explicit 1D decomposition of $\mathbb{R}^1$ into $(-\infty, 1)$,
    $\{1\}$, and $(1, \infty)$. -/
noncomputable def linear1DDecomposition : Decomposition 1 where
  cells := linear1DCylinder.children
  cells_nodup := linear1DCylinder_isPartition.1.2.2.2.1
  cover := by
    intro x
    rcases linear1DCylinder_isPartition.1.1 (Fin.init x) (Set.mem_univ _)
      (x (Fin.last 0)) with ⟨c, hc, hmem⟩
    rw [Fin.snoc_init_self] at hmem
    exact ⟨c, hc, hmem⟩
  pairwise_disjoint := linear1DCylinder_isPartition.1.2.2.1

/-- The explicit 1D CAD for $\{x_0 - 1\}$. -/
noncomputable def linear1DCAD : CAD 1 :=
  .succ baseCAD linear1DDecomposition [linear1DCylinder]

/-- The explicit 1D CAD for $\{x_0 - 1\}$ satisfies `IsCAD`, has $3$ cells,
    and is sign-invariant for $\{x_0 - 1\}$. -/
theorem linear1DCAD_valid :
    IsCAD linear1DCAD ∧
    linear1DCAD.cells.length = 3 ∧
    CADInvariant {linear1DPoly} linear1DCAD.cells := by
  refine ⟨⟨trivial, ?_⟩, linear1DCylinder.children_length,
    linear1D_cells_signInvariant⟩
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro L hL
    have hLeq : L = linear1DCylinder := List.mem_singleton.mp hL
    subst L
    simp [CAD.decomposition, baseCAD, baseDecomposition0,
      linear1DCylinder, Cylinder.canonical]
  · intro c hc
    have hceq : c = baseCell0 := List.mem_singleton.mp hc
    subst c
    exact ⟨linear1DCylinder, by simp, rfl⟩
  · intro L hL M hM _
    rw [List.mem_singleton.mp hL, List.mem_singleton.mp hM]
  · simp [linear1DDecomposition]
  · intro L hL
    rw [List.mem_singleton.mp hL]
    exact linear1DCylinder_isPartition.1

/-- The first-order sentence $\exists x,\, x + (-1) = 0$ and its quantifier-free
    elimination over $\mathbb{R}$. -/
noncomputable def linear1DSentence : orderedRing.Sentence :=
  BoundedFormula.ex
    ((addFunc.apply₂
      (Term.var (Sum.inr (0 : Fin 1)) : orderedRing.Term (Empty ⊕ Fin 1))
      (negFunc.apply₁ (Constants.term oneFunc))).bdEqual
      (Constants.term zeroFunc))

/-- The sentence $\exists x,\, x - 1 = 0$ holds in $\mathbb{R}$, and
    `rcf_sentence_quantifier_elimination` produces a true quantifier-free
    sentence equivalent to it. -/
theorem linear1DSentence_qe_true :
    Sentence.Realize (L := orderedRing) (M := ℝ) linear1DSentence ∧
    ∃ ψ : orderedRing.Sentence,
      ψ.IsQF ∧ Sentence.Realize (L := orderedRing) (M := ℝ) ψ := by
  have hreal : Sentence.Realize (L := orderedRing) (M := ℝ) linear1DSentence := by
    rw [Sentence.Realize, Formula.Realize, linear1DSentence,
      BoundedFormula.realize_ex]
    refine ⟨1, ?_⟩
    change (1 : ℝ) + -1 = 0
    ring
  rcases rcf_sentence_quantifier_elimination linear1DSentence with ⟨ψ, hQF, hiff⟩
  exact ⟨hreal, ψ, hQF, hiff.mp hreal⟩

end CollinsCAD
