import Logic.TermPoly
import CAD.Integrality

namespace CollinsCAD

open FirstOrder FirstOrder.Language Polynomial MvPolynomial

/-- Translate a bounded term into the concatenated CAD coordinates. -/
noncomputable def boundedTermToMvPoly {r k : ℕ}
    (t : orderedRing.Term (Fin r ⊕ Fin k)) : MvPolynomial (Fin (r + k)) ℤ :=
  termToMvPoly (t.relabel (finSumFinEquiv (m := r) (n := k)))

/-- The free coordinates of a concatenated tuple. -/
def freePart {n m : ℕ} (z : Fin (n + m) → ℝ) : Fin n → ℝ :=
  fun i => z (Fin.castAdd m i)

/-- The bound coordinates of a concatenated tuple. -/
def boundPart {n m : ℕ} (z : Fin (n + m) → ℝ) : Fin m → ℝ :=
  fun i => z (Fin.natAdd n i)

/-- Join free and bound coordinates into CAD order. -/
def joinTuple {n m : ℕ} (v : Fin n → ℝ) (xs : Fin m → ℝ) :
    Fin (n + m) → ℝ :=
  fun i => Sum.elim v xs ((finSumFinEquiv (m := n) (n := m)).symm i)

/-- Realize a bounded formula on concatenated CAD coordinates. -/
def boundedRealize {r k : ℕ}
    (φ : orderedRing.BoundedFormula (Fin r) k)
    (z : Fin (r + k) → ℝ) : Prop :=
  φ.Realize (freePart z) (boundPart z)

/-- The free/bound split is exactly the `finSumFinEquiv` assignment. -/
@[simp] theorem sum_elim_freePart_boundPart {n m : ℕ} (z : Fin (n + m) → ℝ) :
    Sum.elim (freePart z) (boundPart z) =
      z ∘ (finSumFinEquiv (m := n) (n := m)) := by
  funext i
  cases i <;> simp [freePart, boundPart]

/-- Joining the free and bound parts recovers the original tuple. -/
@[simp] theorem joinTuple_freePart_boundPart {n m : ℕ} (z : Fin (n + m) → ℝ) :
    joinTuple (freePart z) (boundPart z) = z := by
  funext i
  rcases h : (finSumFinEquiv (m := n) (n := m)).symm i with j | j
  · have hi : i = (finSumFinEquiv (m := n) (n := m)) (Sum.inl j) := by
      rw [← h, Equiv.apply_symm_apply]
    subst i
    simp [joinTuple, freePart]
  · have hi : i = (finSumFinEquiv (m := n) (n := m)) (Sum.inr j) := by
      rw [← h, Equiv.apply_symm_apply]
    subst i
    simp [joinTuple, boundPart]

/-- The free part of a joined tuple is the original free assignment. -/
@[simp] theorem freePart_joinTuple {n m : ℕ} (v : Fin n → ℝ) (xs : Fin m → ℝ) :
    freePart (joinTuple v xs) = v := by
  funext i
  simp [freePart, joinTuple, finSumFinEquiv]

/-- The bound part of a joined tuple is the original bound assignment. -/
@[simp] theorem boundPart_joinTuple {n m : ℕ} (v : Fin n → ℝ) (xs : Fin m → ℝ) :
    boundPart (joinTuple v xs) = xs := by
  funext i
  simp [boundPart, joinTuple, finSumFinEquiv]

/-- Bounded term realization in CAD coordinates. -/
@[simp] theorem boundedTerm_realize {r k : ℕ}
    (t : orderedRing.Term (Fin r ⊕ Fin k)) (z : Fin (r + k) → ℝ) :
    t.realize (z ∘ (finSumFinEquiv (m := r) (n := k))) =
      MvPolynomial.eval z (intCastMv (r + k) (boundedTermToMvPoly t)) := by
  unfold boundedTermToMvPoly
  rw [← Term.realize_relabel]
  exact realize_termToMvPoly_intCast _ z

/-- At bound depth zero, bounded realization is ordinary formula realization. -/
@[simp] theorem boundedRealize_zero {n : ℕ}
    (φ : orderedRing.Formula (Fin n)) (z : Fin n → ℝ) :
    boundedRealize φ z ↔ φ.Realize z := by
  have hfree : freePart (n := n) (m := 0) z = z := by
    funext i
    simp [freePart]
  have hbound : boundPart (n := n) (m := 0) z = default := by
    funext i
    exact Fin.elim0 i
  rw [boundedRealize, Formula.Realize, hfree, hbound]
  have hempty : (@default (Fin 0 → ℝ) Pi.instInhabited) =
      (@default (Fin 0 → ℝ) Unique.instInhabited) := Subsingleton.elim _ _
  rw [hempty]

/-- At bound depth one, bounded realization sees a snoc tuple. -/
@[simp] theorem boundedRealize_snoc_one {r : ℕ}
    (φ : orderedRing.BoundedFormula (Fin r) 1) (a : Fin r → ℝ) (x : ℝ) :
    boundedRealize φ (Fin.snoc a x) ↔ φ.Realize a ![x] := by
  have hfree : (fun i : Fin r =>
      @Fin.snoc r (fun _ => ℝ) a x (Fin.castAdd 1 i)) = a := by
    exact _root_.funext (fun i : Fin r =>
      @Fin.snoc_castSucc r (fun _ => ℝ) x a i)
  have hbound : (fun j : Fin 1 =>
      @Fin.snoc r (fun _ => ℝ) a x (Fin.natAdd r j)) = ![x] := by
    exact _root_.funext (fun j : Fin 1 => by
      fin_cases j
      exact @Fin.snoc_last r (fun _ => ℝ) x a)
  change φ.Realize (fun i : Fin r =>
      @Fin.snoc r (fun _ => ℝ) a x (Fin.castAdd 1 i))
    (fun j : Fin 1 => @Fin.snoc r (fun _ => ℝ) a x (Fin.natAdd r j)) ↔
    φ.Realize a ![x]
  rw [hfree, hbound]

/-- Integer atom polynomials of a bounded formula. Quantifier nodes contribute
    nothing because this support is used only for quantifier-free matrices. -/
noncomputable def atomPolys {r k : ℕ} :
    orderedRing.BoundedFormula (Fin r) k →
      Finset (MvPolynomial (Fin (r + k)) ℤ)
  | .falsum => ∅
  | .equal t₁ t₂ => {boundedTermToMvPoly t₁ - boundedTermToMvPoly t₂}
  | .rel .lt ts => {boundedTermToMvPoly (ts 0) - boundedTermToMvPoly (ts 1)}
  | .imp φ ψ => atomPolys φ ∪ atomPolys ψ
  | .all _ => ∅

/-- Cast integer atom polynomials to real coefficients. -/
noncomputable def realAtomPolys {n : ℕ}
    (A : Finset (MvPolynomial (Fin n) ℤ)) : Finset (MvPolynomial (Fin n) ℝ) :=
  A.image (intCastMv n)

@[simp] theorem mem_realAtomPolys {n : ℕ}
    {A : Finset (MvPolynomial (Fin n) ℤ)} {P : MvPolynomial (Fin n) ℝ} :
    P ∈ realAtomPolys A ↔ ∃ Q ∈ A, intCastMv n Q = P := by
  simp [realAtomPolys, Finset.mem_image]

/-- Atom support is monotone under inclusion. -/
theorem realAtomPolys_mono {n : ℕ} {A B : Finset (MvPolynomial (Fin n) ℤ)}
    (h : A ⊆ B) : realAtomPolys A ⊆ realAtomPolys B := by
  intro P hP
  rcases mem_realAtomPolys.mp hP with ⟨Q, hQ, rfl⟩
  exact mem_realAtomPolys.mpr ⟨Q, h hQ, rfl⟩

/-- Real atom support consists of integral polynomials. -/
theorem isIntPolyFamily_realAtomPolys {n : ℕ}
    (A : Finset (MvPolynomial (Fin n) ℤ)) : IsIntPolyFamily (realAtomPolys A) := by
  intro P hP
  rcases mem_realAtomPolys.mp hP with ⟨Q, hQ, rfl⟩
  exact isIntPoly_map Q

/-- Equality atoms are zero-sign conditions on their difference polynomial. -/
theorem boundedRealize_equal_iff_eval_zero {r k : ℕ}
    (t₁ t₂ : orderedRing.Term (Fin r ⊕ Fin k)) (z : Fin (r + k) → ℝ) :
    boundedRealize (t₁.bdEqual t₂) z ↔
      MvPolynomial.eval z (intCastMv (r + k)
        (boundedTermToMvPoly t₁ - boundedTermToMvPoly t₂)) = 0 := by
  simp only [boundedRealize, BoundedFormula.realize_bdEqual,
    sum_elim_freePart_boundPart, boundedTerm_realize, map_sub, sub_eq_zero]

theorem boundedRealize_equal_iff_sign_zero {r k : ℕ}
    (t₁ t₂ : orderedRing.Term (Fin r ⊕ Fin k)) (z : Fin (r + k) → ℝ) :
    boundedRealize (t₁.bdEqual t₂) z ↔
      SignType.sign (MvPolynomial.eval z (intCastMv (r + k)
        (boundedTermToMvPoly t₁ - boundedTermToMvPoly t₂))) = 0 := by
  exact (boundedRealize_equal_iff_eval_zero t₁ t₂ z).trans sign_eq_zero_iff.symm

/-- Strict-order atoms are negative-sign conditions on their difference
    polynomial. -/
theorem boundedRealize_lt_iff_eval_neg {r k : ℕ}
    (t₁ t₂ : orderedRing.Term (Fin r ⊕ Fin k)) (z : Fin (r + k) → ℝ) :
    boundedRealize (orderedRingTermLt t₁ t₂) z ↔
      MvPolynomial.eval z (intCastMv (r + k)
        (boundedTermToMvPoly t₁ - boundedTermToMvPoly t₂)) < 0 := by
  simp only [boundedRealize, orderedRingTermLt, BoundedFormula.realize_rel₂,
    sum_elim_freePart_boundPart, boundedTerm_realize, orderedRing_relMap_lt,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, sub_lt_zero]

theorem boundedRealize_lt_iff_sign_neg_one {r k : ℕ}
    (t₁ t₂ : orderedRing.Term (Fin r ⊕ Fin k)) (z : Fin (r + k) → ℝ) :
    boundedRealize (orderedRingTermLt t₁ t₂) z ↔
      SignType.sign (MvPolynomial.eval z (intCastMv (r + k)
        (boundedTermToMvPoly t₁ - boundedTermToMvPoly t₂))) = -1 := by
  exact (boundedRealize_lt_iff_eval_neg t₁ t₂ z).trans sign_eq_neg_one_iff.symm

end CollinsCAD
