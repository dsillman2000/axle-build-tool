import Mathlib
import Analysis.Theorem1
import Analysis.Delineability
import Analysis.MonicComplexFiber

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
  let p : S → Polynomial ℂ := monicComplexFiber q d
  have hp_eq (a : S) : p a = (q a).map (algebraMap ℝ ℂ) * Polynomial.C (c a) := rfl
  have hqcoeff : ∀ k : ℕ, Continuous (fun a : S => (q a).coeff k) := by
    intro k
    have hfun : (fun a : S => (q a).coeff k) =
        (fun a : S => MvPolynomial.eval a.1 ((finLastEquiv ℝ r P).coeff k)) := by
      funext a
      simp [q, fiberPoly]
    rw [hfun]
    exact (MvPolynomial.continuous_eval _).comp continuous_subtype_val
  have hcne : ∀ a : S, (q a).coeff d ≠ 0 := fun a => hlc a.1 a.2
  have hcoeff : ∀ k : ℕ, Continuous (fun a : S => (p a).coeff k) :=
    continuous_monicComplexFiber_coeff q hqcoeff d hcne
  have hdegp : ∀ a : S, (p a).natDegree = d :=
    natDegree_monicComplexFiber q d (fun a => hdeg a.1 a.2) hcne
  have hmonicp : ∀ a : S, (p a).Monic :=
    monic_monicComplexFiber q d (fun a => hdeg a.1 a.2) hcne
  have hmp : ∀ a : S, (p a).roots.toFinset.card = m := by
    intro a
    change (monicComplexFiber q d a).roots.toFinset.card = m
    rw [roots_monicComplexFiber q d hcne]
    exact hm a.1 a.2
  have hrealp : ∀ a : S, ∀ k : ℕ, ((p a).coeff k).im = 0 :=
    fun a k => im_coeff_monicComplexFiber q d a k
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
      rw [hp_eq ai] at hz
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
    · have hscale : (p ai).roots = ((q ai).map (algebraMap ℝ ℂ)).roots :=
        roots_monicComplexFiber q d hcne ai
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
      rw [hp_eq ai]
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
