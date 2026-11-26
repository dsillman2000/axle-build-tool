import Mathlib
import Analysis.Theorem1
import Analysis.Delineability

namespace CollinsCAD

open Polynomial

/-- Root multiplicities are preserved when a real polynomial is mapped to
    $\mathbb{C}$. -/
theorem rootMultiplicity_map_eq {q : Polynomial ℝ} (hq : q ≠ 0) (x : ℝ) :
    Polynomial.rootMultiplicity ((algebraMap ℝ ℂ) x)
        (q.map (algebraMap ℝ ℂ)) = Polynomial.rootMultiplicity x q := by
  classical
  have hinj : Function.Injective (algebraMap ℝ ℂ : ℝ → ℂ) := Complex.ofReal_injective
  have hmapne : q.map (algebraMap ℝ ℂ) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hq
  apply le_antisymm
  · have hdiv : (Polynomial.X - Polynomial.C ((algebraMap ℝ ℂ) x)) ^
        Polynomial.rootMultiplicity ((algebraMap ℝ ℂ) x)
          (q.map (algebraMap ℝ ℂ)) ∣ q.map (algebraMap ℝ ℂ) :=
      (Polynomial.le_rootMultiplicity_iff hmapne).mp le_rfl
    have hmappre : Polynomial.map (algebraMap ℝ ℂ)
        ((Polynomial.X - Polynomial.C x) ^
          Polynomial.rootMultiplicity ((algebraMap ℝ ℂ) x)
            (q.map (algebraMap ℝ ℂ))) ∣ Polynomial.map (algebraMap ℝ ℂ) q := by
      simpa using hdiv
    have hdiv' : (Polynomial.X - Polynomial.C x) ^
        Polynomial.rootMultiplicity ((algebraMap ℝ ℂ) x)
          (q.map (algebraMap ℝ ℂ)) ∣ q :=
      (Polynomial.map_dvd_map' (algebraMap ℝ ℂ)).mp hmappre
    exact (Polynomial.le_rootMultiplicity_iff hq).mpr hdiv'
  · have hdiv : (Polynomial.X - Polynomial.C x) ^ Polynomial.rootMultiplicity x q ∣ q :=
      (Polynomial.le_rootMultiplicity_iff hq).mp le_rfl
    have hmapdiv := Polynomial.map_dvd (algebraMap ℝ ℂ) hdiv
    have hdiv' : (Polynomial.X - Polynomial.C ((algebraMap ℝ ℂ) x)) ^
        Polynomial.rootMultiplicity x q ∣ q.map (algebraMap ℝ ℂ) := by
      simpa using hmapdiv
    exact (Polynomial.le_rootMultiplicity_iff hmapne).mpr hdiv'

/-- A polynomial whose fibres are nonzero constants has no real roots and is
    therefore real-delineable with the empty root family. -/
theorem isRealDelineable_of_fiber_natDegree_eq_zero
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℝ) (S : Set (Fin r → ℝ))
    (hdeg0 : ∀ a ∈ S, (fiberPoly r P a).natDegree = 0)
    (hne : ∀ a ∈ S, fiberPoly r P a ≠ 0) :
    IsRealDelineable P S := by
  refine ⟨0, (fun i : Fin 0 => Fin.elim0 i), (fun i : Fin 0 => Fin.elim0 i),
    ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro a ha x hx
    exfalso
    have hc : fiberPoly r P a = Polynomial.C ((fiberPoly r P a).coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (hdeg0 a ha)
    have hc0 : (fiberPoly r P a).coeff 0 ≠ 0 := by
      intro hz
      exact hne a ha (by rw [hc, hz, Polynomial.C_0])
    rw [hc, Polynomial.eval_C] at hx
    exact hc0 hx
  · intro i
    exact Fin.elim0 i

/-- Collins' Theorem 1 (real-root form) for a real polynomial in $r+1$
    variables: if the leading coefficient does not vanish on a connected set
    $S$ and the number of distinct complex roots of each fibre is invariant,
    then the real roots are delineable on $S$. -/
theorem delineability_theorem_1_real_mv
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℝ)
    (S : Set (Fin r → ℝ)) (hS : IsConnected S)
    (d m : ℕ) (hd : 0 < d)
    (hdeg : ∀ a ∈ S, (fiberPoly r P a).natDegree = d)
    (hlc : ∀ a ∈ S, (fiberPoly r P a).coeff d ≠ 0)
    (hm : ∀ a ∈ S, ((fiberPoly r P a).map (algebraMap ℝ ℂ)).roots.toFinset.card = m) :
    IsRealDelineable P S := by
  classical
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS.isPreconnected
  obtain ⟨a0, ha0⟩ := hS.nonempty
  let : Nonempty S := ⟨⟨a0, ha0⟩⟩
  let q : S → Polynomial ℝ := fun a => fiberPoly r P a.1
  let c : S → ℂ := fun a => (algebraMap ℝ ℂ ((q a).coeff d))⁻¹
  let p : S → Polynomial ℂ := fun a => (q a).map (algebraMap ℝ ℂ) * Polynomial.C (c a)
  have hqcoeff : ∀ k : ℕ, Continuous (fun a : S => (q a).coeff k) := by
    intro k
    have hfun : (fun a : S => (q a).coeff k) =
        (fun a : S => MvPolynomial.eval a.1 ((finLastEquiv ℝ r P).coeff k)) := by
      funext a
      simp [q, fiberPoly]
    rw [hfun]
    exact (MvPolynomial.continuous_eval _).comp continuous_subtype_val
  have hclc : Continuous (fun a : S => (q a).coeff d) := hqcoeff d
  have hcne : ∀ a : S, (q a).coeff d ≠ 0 := fun a => hlc a.1 a.2
  have hccont : Continuous c := by
    dsimp [c]
    exact (Complex.continuous_ofReal.comp hclc).inv₀
      (fun a => Complex.ofReal_ne_zero.mpr (hcne a))
  have hcoeff : ∀ k : ℕ, Continuous (fun a : S => (p a).coeff k) := by
    intro k
    dsimp [p]
    by_cases hk : k ≤ d
    · have h1 : Continuous (fun a : S =>
          (algebraMap ℝ ℂ ((q a).coeff k))) :=
        Complex.continuous_ofReal.comp (hqcoeff k)
      have hcoeff_eq : (fun a : S => (p a).coeff k) =
          (fun a : S => (algebraMap ℝ ℂ) ((q a).coeff k) * c a) := by
        funext a
        simp [p, Polynomial.coeff_mul_C]
      rw [hcoeff_eq]
      exact h1.mul hccont
    · have hgt : d < k := Nat.lt_of_not_ge hk
      have hzeroq : ∀ a : S, (q a).coeff k = 0 := by
        intro a
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [q, hdeg a.1 a.2] using hgt)
      simpa [Polynomial.coeff_mul_C, hzeroq] using
        (continuous_const : Continuous (fun _ : S => (0 : ℂ)))
  have hdegp : ∀ a : S, (p a).natDegree = d := by
    intro a
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · dsimp [p]
      calc
        ((q a).map (algebraMap ℝ ℂ) * Polynomial.C (c a)).natDegree
            ≤ ((q a).map (algebraMap ℝ ℂ)).natDegree := Polynomial.natDegree_mul_C_le _ _
        _ = (q a).natDegree := by
          exact Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective (q a)
        _ = d := hdeg a.1 a.2
    · have hc : c a ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (hcne a))
      dsimp [p, c]
      have hc' : (algebraMap ℝ ℂ) ((q a).coeff d) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (hcne a)
      simpa [Polynomial.coeff_mul_C, c] using mul_ne_zero hc' (inv_ne_zero hc')
  have hmonicp : ∀ a : S, (p a).Monic := by
    intro a
    exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one d (le_of_eq (hdegp a)) (by
      have hc : (algebraMap ℝ ℂ) ((q a).coeff d) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (hcne a)
      dsimp [p, c]
      simpa [Polynomial.coeff_mul_C] using mul_inv_cancel₀ hc)
  have hmp : ∀ a : S, (p a).roots.toFinset.card = m := by
    intro a
    have hroots : (p a).roots = ((q a).map (algebraMap ℝ ℂ)).roots := by
      dsimp [p]
      rw [mul_comm, Polynomial.roots_C_mul]
      exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (hcne a))
    rw [hroots]
    exact hm a.1 a.2
  have hrealp : ∀ a : S, ∀ k : ℕ, ((p a).coeff k).im = 0 := by
    intro a k
    have hcoeff_val : (p a).coeff k =
        (algebraMap ℝ ℂ) ((q a).coeff k) * c a := by
      simp [p, Polynomial.coeff_mul_C]
    rw [hcoeff_val]
    simp [c]
  obtain ⟨k, f, e, hfcont, hfroot, hfexhaust, hfmono⟩ :=
    delineability_theorem_1_real p hcoeff d m hd hdegp hmonicp hmp hrealp
  let F : Fin k → (Fin r → ℝ) → ℝ := fun i a => if ha : a ∈ S then f i ⟨a, ha⟩ else 0
  refine ⟨k, F, e, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [continuousOn_iff_continuous_domRestrict]
    simpa [F] using hfcont i
  · intro i a ha
    let ai : S := ⟨a, ha⟩
    have hcai : c ai ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (hcne ai))
    have hqne : q ai ≠ 0 := by
      intro hzero
      have : (q ai).coeff d = 0 := by simp [hzero]
      exact hcne ai this
    refine ⟨(hfroot i ai).1, ?_, ?_⟩
    · have hz := (hfroot i ai).2.1
      rw [Polynomial.IsRoot.def] at hz
      dsimp [p] at hz
      rw [Polynomial.eval_mul, Polynomial.eval_C] at hz
      have hevalmap : Polynomial.eval ((f i ai : ℝ) : ℂ)
          ((q ai).map (algebraMap ℝ ℂ)) =
          (algebraMap ℝ ℂ) (Polynomial.eval (f i ai) (q ai)) := by
        rw [Polynomial.eval_map]
        exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (f i ai) (q ai)
      rw [hevalmap] at hz
      have hcastzero : (algebraMap ℝ ℂ) (Polynomial.eval (f i ai) (q ai)) = 0 := by
        exact (mul_eq_zero.mp hz).resolve_right hcai
      have hrealzero : Polynomial.eval (f i ai) (q ai) = 0 :=
        Complex.ofReal_injective hcastzero
      simpa [F, ha, q] using hrealzero
    · have hscale : (p ai).roots = ((q ai).map (algebraMap ℝ ℂ)).roots := by
        dsimp [p]
        rw [mul_comm, Polynomial.roots_C_mul _ hcai]
      have hrp_scale : Polynomial.rootMultiplicity ((f i ai : ℝ) : ℂ) (p ai) =
          Polynomial.rootMultiplicity ((f i ai : ℝ) : ℂ)
            ((q ai).map (algebraMap ℝ ℂ)) := by
        rw [← Polynomial.count_roots (p ai), ← Polynomial.count_roots
          ((q ai).map (algebraMap ℝ ℂ)), hscale]
      have hgoal : Polynomial.rootMultiplicity (F i a) (fiberPoly r P a) =
          Polynomial.rootMultiplicity (f i ai) (q ai) := by
        simp [F, ha, ai, q]
      rw [hgoal]
      calc
        Polynomial.rootMultiplicity (f i ai) (q ai)
            = Polynomial.rootMultiplicity ((f i ai : ℝ) : ℂ)
                ((q ai).map (algebraMap ℝ ℂ)) := (rootMultiplicity_map_eq hqne (f i ai)).symm
        _ = Polynomial.rootMultiplicity ((f i ai : ℝ) : ℂ) (p ai) := hrp_scale.symm
        _ = e i := (hfroot i ai).2.2
  · intro a ha x hx
    let ai : S := ⟨a, ha⟩
    have hrootR : (q ai).IsRoot x := by
      rw [Polynomial.IsRoot.def]
      simpa [q] using hx
    have hrootC : ((q ai).map (algebraMap ℝ ℂ)).IsRoot ((algebraMap ℝ ℂ) x) :=
      hrootR.map (algebraMap ℝ ℂ)
    have hrootP : (p ai).IsRoot ((algebraMap ℝ ℂ) x) := by
      dsimp [p]
      exact Polynomial.root_mul_right_of_isRoot (Polynomial.C (c ai)) hrootC
    rcases hfexhaust ai ((algebraMap ℝ ℂ) x) hrootP (by simp) with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hi' : ((f i ai : ℝ) : ℂ) = ((algebraMap ℝ ℂ) x) := hi
    have hreal : (f i ai : ℂ) = ((algebraMap ℝ ℂ) x) := by simpa using hi'
    have hEq : f i ai = x := Complex.ofReal_injective hreal
    simpa [F, ha] using hEq
  · intro i j a ha hij
    simpa [F, ha] using hfmono i j ⟨a, ha⟩ hij

end CollinsCAD
