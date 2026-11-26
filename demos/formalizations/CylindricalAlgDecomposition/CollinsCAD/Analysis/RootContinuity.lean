import Mathlib

namespace CollinsCAD

open Polynomial Filter

/-!
## Continuity of the multiset of roots

The two ingredients needed for Collins' Theorem 1 are a Cauchy bound on the
roots of a monic polynomial and the fact that the roots cannot escape to
infinity or split across a prescribed separation under a small perturbation of
the coefficients. The latter is proved by a Vieta--compactness argument, so it
avoids any appeal to Rouché's theorem.
-/

/-- **Cauchy bound.** Every root $z$ of a monic polynomial $P$ of positive
    degree satisfies $\|z\| \le \max 1 \sum_{k < \deg P} \|P_k\|$. -/
theorem cauchy_root_bound {P : Polynomial ℂ} (hmonic : P.Monic)
    (hd : 0 < P.natDegree) {z : ℂ} (hz : P.IsRoot z) :
    ‖z‖ ≤ max 1 (∑ k ∈ Finset.range P.natDegree, ‖P.coeff k‖) := by
  let d := P.natDegree
  let M : ℝ := ∑ k ∈ Finset.range d, ‖P.coeff k‖
  have hd' : 0 < d := by simpa [d] using hd
  by_cases hzle : ‖z‖ ≤ 1
  · exact hzle.trans (le_max_left _ _)
  · have hzgt : 1 < ‖z‖ := lt_of_not_ge hzle
    have hMnonneg : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hEval := Polynomial.eval_eq_sum_range (p := P) z
    rw [hz] at hEval
    rw [Finset.sum_range_succ] at hEval
    have hcoeff : P.coeff d = 1 := by simpa [d] using hmonic.coeff_natDegree
    rw [hcoeff] at hEval
    have hsum : (∑ k ∈ Finset.range d, P.coeff k * z ^ k) + z ^ d = 0 := by
      simpa [mul_comm, d] using hEval.symm
    have hzd : z ^ d = -(∑ k ∈ Finset.range d, P.coeff k * z ^ k) :=
      (add_eq_zero_iff_eq_neg').mp hsum
    have hpow_le : ‖z‖ ^ d ≤ M * ‖z‖ ^ (d - 1) := by
      have hnormpow : ‖z‖ ^ d = ‖z ^ d‖ := (norm_pow z d).symm
      rw [hnormpow, hzd, norm_neg]
      calc
        ‖∑ k ∈ Finset.range d, P.coeff k * z ^ k‖
            ≤ ∑ k ∈ Finset.range d, ‖P.coeff k * z ^ k‖ := norm_sum_le _ _
        _ = ∑ k ∈ Finset.range d, ‖P.coeff k‖ * ‖z‖ ^ k := by simp [norm_pow]
        _ ≤ ∑ k ∈ Finset.range d, ‖P.coeff k‖ * ‖z‖ ^ (d - 1) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (le_of_lt hzgt)
              (Nat.le_pred_of_lt (Finset.mem_range.mp hk))) (norm_nonneg _)
        _ = M * ‖z‖ ^ (d - 1) := by simp [M, Finset.sum_mul]
    have hpowpos : 0 < ‖z‖ ^ (d - 1) := pow_pos (lt_trans zero_lt_one hzgt) _
    have hpow_eq : ‖z‖ ^ d = ‖z‖ ^ (d - 1) * ‖z‖ := by
      rcases d with _ | d'
      · omega
      · simp [pow_succ]
    rw [hpow_eq] at hpow_le
    have hle : ‖z‖ ≤ M := by
      have hle' : ‖z‖ * ‖z‖ ^ (d - 1) ≤ M * ‖z‖ ^ (d - 1) := by
        simpa [mul_comm] using hpow_le
      exact (mul_le_mul_iff_of_pos_right hpowpos).mp hle'
    exact hle.trans (le_max_right _ _)

/-- The monic polynomial of degree $d$ whose coefficient vector is $v$. -/
noncomputable def polyOfCoeffs (d : ℕ) (v : Fin (d + 1) → ℂ) : Polynomial ℂ :=
  ∑ i : Fin (d + 1), Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)

/-- The $k$-th coefficient of `polyOfCoeffs`, for all $k$. -/
theorem coeff_polyOfCoeffs (d : ℕ) (v : Fin (d + 1) → ℂ) (k : ℕ) :
    (polyOfCoeffs d v).coeff k = if h : k ≤ d then v ⟨k, Nat.lt_succ_of_le h⟩ else 0 := by
  classical
  simp [polyOfCoeffs]
  by_cases hk : k ≤ d
  · let i : Fin (d + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    have hsum : (∑ x : Fin (d + 1), if k = (x : ℕ) then v x else 0) = v i := by
      simpa [i] using
        (Fintype.sum_eq_single (f := fun x : Fin (d + 1) => if k = (x : ℕ) then v x else 0) i (by
          intro b hbi
          have hne : k ≠ (b : ℕ) := by
            intro h
            apply hbi
            apply Fin.ext
            simpa [i] using h.symm
          simp [hne]))
    simpa [hk, i] using hsum
  · have hgt : d < k := Nat.lt_of_not_ge hk
    have hsum : (∑ x : Fin (d + 1), if k = (x : ℕ) then v x else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hne : k ≠ (x : ℕ) := by omega
      simp [hne]
    simpa [hk] using hsum

/-- If $P$ has degree at most $d$, rebuilding it from its first $d+1$
    coefficients returns $P$. -/
theorem polyOfCoeffs_self {P : Polynomial ℂ} {d : ℕ} (hd : P.natDegree ≤ d) :
    polyOfCoeffs d (fun i : Fin (d + 1) => P.coeff (i : ℕ)) = P := by
  classical
  apply AddMonoidAlgebra.ext
  ext k
  by_cases hk : k ≤ d
  · simp [coeff_polyOfCoeffs, hk]
  · have hgt : d < k := Nat.lt_of_not_ge hk
    have hzero : P.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hgt)
    simp [coeff_polyOfCoeffs, hk, hzero]

/-- The monic polynomial of degree $d$ with the given roots $w_i$. -/
noncomputable def rootPoly (d : ℕ) (w : Fin d → ℂ) : Polynomial ℂ :=
  ∏ i : Fin d, (Polynomial.X - Polynomial.C (w i))

/-- Evaluating `rootPoly` at $x$ gives the product of $x-w_i$. -/
theorem rootPoly_eval (d : ℕ) (w : Fin d → ℂ) (x : ℂ) :
    Polynomial.eval x (rootPoly d w) = ∏ i : Fin d, (x - w i) := by
  change (Polynomial.evalRingHom x) (∏ i : Fin d, (Polynomial.X - Polynomial.C (w i))) = _
  rw [map_prod]
  simp

/-- Evaluation of `rootPoly` at a fixed point is continuous in the roots. -/
theorem continuous_rootPoly_eval (d : ℕ) (x : ℂ) :
    Continuous (fun w : Fin d → ℂ => Polynomial.eval x (rootPoly d w)) := by
  simp only [rootPoly_eval]
  fun_prop

/-- Evaluating a polynomial rebuilt from a coefficient vector is the finite sum
    of the coefficients times the corresponding powers of $x$. -/
theorem eval_polyOfCoeffs_eq_sum (d : ℕ) (v : Fin (d + 1) → ℂ) (x : ℂ) :
    Polynomial.eval x (polyOfCoeffs d v) = ∑ i : Fin (d + 1), v i * x ^ (i : ℕ) := by
  change (Polynomial.evalRingHom x) (∑ i : Fin (d + 1),
    Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)) = _
  rw [map_sum]
  simp

/-- If coefficient vectors converge pointwise, so do the evaluations at any
    fixed point of the polynomials they determine. -/
theorem tendsto_eval_polyOfCoeffs {d : ℕ} {vseq : ℕ → Fin (d + 1) → ℂ}
    {v : Fin (d + 1) → ℂ} (hv : Tendsto vseq atTop (nhds v)) (x : ℂ) :
    Tendsto (fun n => Polynomial.eval x (polyOfCoeffs d (vseq n))) atTop
      (nhds (Polynomial.eval x (polyOfCoeffs d v))) := by
  simp only [eval_polyOfCoeffs_eq_sum]
  have hcont : Continuous
      (fun v : Fin (d + 1) → ℂ => ∑ i : Fin (d + 1), v i * x ^ (i : ℕ)) := by
    fun_prop
  exact (hcont.tendsto v).comp hv

/-- Continuity of a single root: a root $\alpha$ of a monic polynomial forces
    every sufficiently nearby monic polynomial of the same degree to have a
    root in any prescribed neighbourhood of $\alpha$. -/
theorem exists_root_near_of_coeff_close
    (P0 : Polynomial ℂ) (_hmonic0 : P0.Monic) (hd0 : 0 < P0.natDegree)
    (α : ℂ) (hαroot : P0.IsRoot α) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ P : Polynomial ℂ, P.Monic → P.natDegree = P0.natDegree →
      (∀ k ≤ P0.natDegree, ‖P.coeff k - P0.coeff k‖ < δ) →
      ∃ z : ℂ, P.IsRoot z ∧ dist z α < ε := by
  classical
  let d := P0.natDegree
  let M0 : ℝ := ∑ k ∈ Finset.range d, ‖P0.coeff k‖
  let B : ℝ := max 1 M0 + d + 1
  by_contra hbad
  push Not at hbad
  have hseq : ∀ n : ℕ, ∃ P : Polynomial ℂ, P.Monic ∧ P.natDegree = d ∧
      (∀ k ≤ d, ‖P.coeff k - P0.coeff k‖ < (1 : ℝ) / (n + 1)) ∧
      ¬ ∃ z : ℂ, P.IsRoot z ∧ dist z α < ε := by
    intro n
    simpa [d] using hbad ((1 : ℝ) / (n + 1)) (by positivity)
  choose Pseq hmonicP hdegP hcloseP hnoroot using hseq
  have hrootcard : ∀ n, (Pseq n).roots.card = d := by
    intro n
    have hc := Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits (Pseq n))
    simpa [hdegP n, d] using hc.symm
  let lseq : ℕ → List ℂ := fun n => (Pseq n).roots.toList
  have hlen : ∀ n, (lseq n).length = d := by
    intro n
    simpa [lseq, Multiset.length_toList] using hrootcard n
  let zseq : ℕ → (Fin d → ℂ) := fun n i =>
    (lseq n).get ⟨i, by simp [hlen n]⟩
  have hofn : ∀ n, List.ofFn (zseq n) = lseq n := by
    intro n
    simpa [zseq, hlen n] using (List.ofFn_get (lseq n))
  have hzroot : ∀ n i, (Pseq n).IsRoot (zseq n i) := by
    intro n i
    apply Polynomial.isRoot_of_mem_roots
    have hm : zseq n i ∈ lseq n := by
      exact List.get_mem (lseq n) ⟨i, by simp [hlen n]⟩
    simpa [lseq] using (Multiset.mem_toList.mp hm)
  have hbound : ∀ n i, ‖zseq n i‖ ≤ B := by
    intro n i
    have hb := cauchy_root_bound (hmonicP n) (by simpa [hdegP n, d] using hd0) (hzroot n i)
    have hMle : (∑ k ∈ Finset.range d, ‖(Pseq n).coeff k‖) ≤ M0 + d := by
      calc
        (∑ k ∈ Finset.range d, ‖(Pseq n).coeff k‖)
            ≤ ∑ k ∈ Finset.range d, (‖P0.coeff k‖ + 1) := by
              apply Finset.sum_le_sum
              intro k hk
              have hk' : k ≤ d := le_of_lt (Finset.mem_range.mp hk)
              have hc := hcloseP n k hk'
              have hc1 : ‖(Pseq n).coeff k - P0.coeff k‖ ≤ 1 := by
                have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
                have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
                have hle1 : (1 : ℝ) / (n + 1) ≤ 1 := by
                  exact (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2 hn1
                exact (lt_of_lt_of_le hc hle1).le
              calc
                ‖(Pseq n).coeff k‖ = ‖((Pseq n).coeff k - P0.coeff k) + P0.coeff k‖ := by ring_nf
                _ ≤ ‖(Pseq n).coeff k - P0.coeff k‖ + ‖P0.coeff k‖ := norm_add_le _ _
                _ ≤ ‖P0.coeff k‖ + 1 := by linarith
        _ = M0 + d := by simp [M0, Finset.sum_add_distrib]
    have hle1 : max 1 (∑ k ∈ Finset.range d, ‖(Pseq n).coeff k‖) ≤ max 1 (M0 + d) := by
      gcongr
    have hle2 : max 1 (M0 + d) ≤ B := by
      have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have hle_a : max 1 (M0 + d) ≤ max 1 M0 + d := by
        apply max_le
        · nlinarith [le_max_left (1 : ℝ) M0]
        · nlinarith [le_max_right (1 : ℝ) M0]
      dsimp [B]
      nlinarith
    have hb' : ‖zseq n i‖ ≤ max 1 (∑ k ∈ Finset.range d, ‖(Pseq n).coeff k‖) := by
      simpa [hdegP n, d] using hb
    exact hb'.trans (hle1.trans hle2)
  let K : Set (Fin d → ℂ) := {w | ∀ i, w i ∈ Metric.closedBall (0 : ℂ) B}
  have hKcpt : IsCompact K := by
    have hc : ∀ i : Fin d, IsCompact (Metric.closedBall (0 : ℂ) B) :=
      fun _ => ProperSpace.isCompact_closedBall 0 B
    simpa [K, Set.pi] using (isCompact_univ_pi hc)
  have hzmem : ∀ n, zseq n ∈ K := by
    intro n i
    simpa [Metric.mem_closedBall, dist_eq_norm] using hbound n i
  rcases hKcpt.tendsto_subseq hzmem with ⟨w, hwK, φ, hφmono, hφtend⟩
  let vseq : ℕ → Fin (d + 1) → ℂ := fun n k => (Pseq n).coeff (k : ℕ)
  let v0 : Fin (d + 1) → ℂ := fun k => P0.coeff (k : ℕ)
  have hvseq : Tendsto vseq atTop (nhds v0) := by
    rw [tendsto_pi_nhds]
    intro k
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
    refine ⟨N, ?_⟩
    intro n hn
    have hle : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
      gcongr
    have hc := hcloseP n (k : ℕ) (by
      have hklt : (k : ℕ) < d + 1 := k.isLt
      exact Nat.le_of_lt_succ hklt)
    have : dist (vseq n k) (v0 k) = ‖(Pseq n).coeff (k : ℕ) - P0.coeff (k : ℕ)‖ := by
      simp [vseq, v0, dist_eq_norm]
    rw [this]
    exact lt_of_lt_of_le hc (hle.trans (le_of_lt hN))
  have hpseq : ∀ n, polyOfCoeffs d (vseq n) = Pseq n := by
    intro n
    apply polyOfCoeffs_self
    simpa [vseq, d] using le_of_eq (hdegP n)
  have hv0poly : polyOfCoeffs d v0 = P0 := by
    apply polyOfCoeffs_self
    simp [d]
  have hrootPoly_eq : rootPoly d w = P0 := by
    apply Polynomial.funext
    intro x
    have hlim1 : Tendsto (fun n => Polynomial.eval x (Pseq (φ n))) atTop
        (nhds (Polynomial.eval x P0)) := by
      have hvφ : Tendsto (fun n => vseq (φ n)) atTop (nhds v0) :=
        hvseq.comp hφmono.tendsto_atTop
      simpa [hpseq, hv0poly] using (tendsto_eval_polyOfCoeffs hvφ x)
    have hlim2 : Tendsto
        (fun n => Polynomial.eval x (rootPoly d (zseq (φ n)))) atTop
        (nhds (Polynomial.eval x (rootPoly d w))) :=
      ((continuous_rootPoly_eval d x).tendsto w).comp hφtend
    have heqseq : ∀ n, Polynomial.eval x (rootPoly d (zseq (φ n))) =
        Polynomial.eval x (Pseq (φ n)) := by
      intro n
      rw [rootPoly_eval]
      have hms : Multiset.map (zseq (φ n)) Finset.univ.val = (Pseq (φ n)).roots := by
        rw [Fin.univ_val_map, hofn]
        simp [lseq]
      have hprod : ((Pseq (φ n)).roots.map (fun r => x - r)).prod =
          ∏ i : Fin d, (x - zseq (φ n) i) := by
        rw [← hms, Multiset.map_map]
        exact (Finset.prod_eq_multiset_prod Finset.univ
          (fun i : Fin d => x - zseq (φ n) i)).symm
      rw [Polynomial.Splits.eval_eq_prod_roots_of_monic
        (IsAlgClosed.splits (Pseq (φ n))) (hmonicP (φ n)) x]
      exact hprod.symm
    exact tendsto_nhds_unique_of_eventuallyEq hlim2 hlim1
      (Eventually.of_forall heqseq)
  have hwroot : ∃ i : Fin d, w i = α := by
    have heval : Polynomial.eval α (rootPoly d w) = 0 := by simpa [hrootPoly_eq] using hαroot
    rw [rootPoly_eval] at heval
    rw [Finset.prod_eq_zero_iff] at heval
    rcases heval with ⟨i, hi, hzero⟩
    refine ⟨i, ?_⟩
    exact (sub_eq_zero.mp hzero).symm
  rcases hwroot with ⟨i, hi⟩
  have hzi_tend : Tendsto (fun n => zseq (φ n) i) atTop (nhds (w i)) := by
    exact hφtend.apply_nhds i
  rw [hi] at hzi_tend
  rw [Metric.tendsto_atTop] at hzi_tend
  obtain ⟨N, hN⟩ := hzi_tend ε hε
  have hnroot := hnoroot (φ N)
  apply hnroot
  refine ⟨zseq (φ N) i, hzroot (φ N) i, ?_⟩
  exact hN N le_rfl

/-- **Exact root count in a ball.** Let $\alpha$ be a root of a monic $P_0$ and
    let $\varepsilon$ separate $\alpha$ from the other distinct roots. Then every
    sufficiently close monic polynomial of the same degree has exactly as many
    roots (counted with multiplicity) in the ball $B(\alpha,\varepsilon)$ as
    $P_0$ has at $\alpha$. -/
theorem roots_count_in_ball_eq_of_coeff_close
    (P0 : Polynomial ℂ) (_hmonic0 : P0.Monic) (hd0 : 0 < P0.natDegree)
    (α : ℂ) (_hαroot : P0.IsRoot α)
    (ε : ℝ) (hε : 0 < ε)
    (hsep : ∀ β ∈ P0.roots.toFinset, β ≠ α → 2 * ε ≤ dist β α) :
    ∃ δ > 0, ∀ P : Polynomial ℂ, P.Monic → P.natDegree = P0.natDegree →
      (∀ k ≤ P0.natDegree, ‖P.coeff k - P0.coeff k‖ < δ) →
      (P.roots.filter (fun z => dist z α < ε)).card = P0.roots.count α := by
  classical
  let d := P0.natDegree
  let M0 : ℝ := ∑ k ∈ Finset.range d, ‖P0.coeff k‖
  let B : ℝ := max 1 M0 + d + 1
  by_contra hbad
  push Not at hbad
  have hseq : ∀ n : ℕ, ∃ P : Polynomial ℂ, P.Monic ∧ P.natDegree = d ∧
      (∀ k ≤ d, ‖P.coeff k - P0.coeff k‖ < (1 : ℝ) / (n + 1)) ∧
      (P.roots.filter (fun z => dist z α < ε)).card ≠ P0.roots.count α := by
    intro n
    simpa [d] using hbad ((1 : ℝ) / (n + 1)) (by positivity)
  choose Pseq hmonicP hdegP hcloseP hbadP using hseq
  have hrootcard : ∀ n, (Pseq n).roots.card = d := by
    intro n
    have hc := Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits (Pseq n))
    simpa [hdegP n, d] using hc.symm
  let lseq : ℕ → List ℂ := fun n => (Pseq n).roots.toList
  have hlen : ∀ n, (lseq n).length = d := by
    intro n
    simpa [lseq, Multiset.length_toList] using hrootcard n
  let zseq : ℕ → (Fin d → ℂ) := fun n i =>
    (lseq n).get ⟨i, by simp [hlen n]⟩
  have hofn : ∀ n, List.ofFn (zseq n) = lseq n := by
    intro n
    simpa [zseq, hlen n] using (List.ofFn_get (lseq n))
  have hzroot : ∀ n i, (Pseq n).IsRoot (zseq n i) := by
    intro n i
    apply Polynomial.isRoot_of_mem_roots
    have hm : zseq n i ∈ lseq n := by
      exact List.get_mem (lseq n) ⟨i, by simp [hlen n]⟩
    simpa [lseq] using (Multiset.mem_toList.mp hm)
  have hbound : ∀ n i, ‖zseq n i‖ ≤ B := by
    intro n i
    have hb := cauchy_root_bound (hmonicP n) (by simpa [hdegP n, d] using hd0) (hzroot n i)
    have hMle : (∑ k ∈ Finset.range d, ‖(Pseq n).coeff k‖) ≤ M0 + d := by
      calc
        (∑ k ∈ Finset.range d, ‖(Pseq n).coeff k‖)
            ≤ ∑ k ∈ Finset.range d, (‖P0.coeff k‖ + 1) := by
              apply Finset.sum_le_sum
              intro k hk
              have hk' : k ≤ d := le_of_lt (Finset.mem_range.mp hk)
              have hc := hcloseP n k hk'
              have hc1 : ‖(Pseq n).coeff k - P0.coeff k‖ ≤ 1 := by
                have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
                have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
                have hle1 : (1 : ℝ) / (n + 1) ≤ 1 := by
                  exact (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2 hn1
                exact (lt_of_lt_of_le hc hle1).le
              calc
                ‖(Pseq n).coeff k‖ = ‖((Pseq n).coeff k - P0.coeff k) + P0.coeff k‖ := by ring_nf
                _ ≤ ‖(Pseq n).coeff k - P0.coeff k‖ + ‖P0.coeff k‖ := norm_add_le _ _
                _ ≤ ‖P0.coeff k‖ + 1 := by linarith
        _ = M0 + d := by simp [M0, Finset.sum_add_distrib]
    have hle1 : max 1 (∑ k ∈ Finset.range d, ‖(Pseq n).coeff k‖) ≤ max 1 (M0 + d) := by
      gcongr
    have hle2 : max 1 (M0 + d) ≤ B := by
      have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have hle_a : max 1 (M0 + d) ≤ max 1 M0 + d := by
        apply max_le
        · nlinarith [le_max_left (1 : ℝ) M0]
        · nlinarith [le_max_right (1 : ℝ) M0]
      dsimp [B]
      nlinarith
    have hb' : ‖zseq n i‖ ≤ max 1 (∑ k ∈ Finset.range d, ‖(Pseq n).coeff k‖) := by
      simpa [hdegP n, d] using hb
    exact hb'.trans (hle1.trans hle2)
  let K : Set (Fin d → ℂ) := {w | ∀ i, w i ∈ Metric.closedBall (0 : ℂ) B}
  have hKcpt : IsCompact K := by
    have hc : ∀ i : Fin d, IsCompact (Metric.closedBall (0 : ℂ) B) :=
      fun _ => ProperSpace.isCompact_closedBall 0 B
    simpa [K, Set.pi] using (isCompact_univ_pi hc)
  have hzmem : ∀ n, zseq n ∈ K := by
    intro n i
    simpa [Metric.mem_closedBall, dist_eq_norm] using hbound n i
  rcases hKcpt.tendsto_subseq hzmem with ⟨w, hwK, φ, hφmono, hφtend⟩
  let vseq : ℕ → Fin (d + 1) → ℂ := fun n k => (Pseq n).coeff (k : ℕ)
  let v0 : Fin (d + 1) → ℂ := fun k => P0.coeff (k : ℕ)
  have hvseq : Tendsto vseq atTop (nhds v0) := by
    rw [tendsto_pi_nhds]
    intro k
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
    refine ⟨N, ?_⟩
    intro n hn
    have hle : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
      gcongr
    have hc := hcloseP n (k : ℕ) (by
      exact Nat.le_of_lt_succ k.isLt)
    have hdist : dist (vseq n k) (v0 k) = ‖(Pseq n).coeff (k : ℕ) - P0.coeff (k : ℕ)‖ := by
      simp [vseq, v0, dist_eq_norm]
    rw [hdist]
    exact lt_of_lt_of_le hc (hle.trans (le_of_lt hN))
  have hpseq : ∀ n, polyOfCoeffs d (vseq n) = Pseq n := by
    intro n
    apply polyOfCoeffs_self
    simpa [vseq, d] using le_of_eq (hdegP n)
  have hv0poly : polyOfCoeffs d v0 = P0 := by
    apply polyOfCoeffs_self
    simp [d]
  have hrootPoly_eq : rootPoly d w = P0 := by
    apply Polynomial.funext
    intro x
    have hlim1 : Tendsto (fun n => Polynomial.eval x (Pseq (φ n))) atTop
        (nhds (Polynomial.eval x P0)) := by
      have hvφ : Tendsto (fun n => vseq (φ n)) atTop (nhds v0) :=
        hvseq.comp hφmono.tendsto_atTop
      simpa [hpseq, hv0poly] using (tendsto_eval_polyOfCoeffs hvφ x)
    have hlim2 : Tendsto
        (fun n => Polynomial.eval x (rootPoly d (zseq (φ n)))) atTop
        (nhds (Polynomial.eval x (rootPoly d w))) :=
      ((continuous_rootPoly_eval d x).tendsto w).comp hφtend
    have heqseq : ∀ n, Polynomial.eval x (rootPoly d (zseq (φ n))) =
        Polynomial.eval x (Pseq (φ n)) := by
      intro n
      rw [rootPoly_eval]
      have hms : Multiset.map (zseq (φ n)) Finset.univ.val = (Pseq (φ n)).roots := by
        rw [Fin.univ_val_map, hofn]
        simp [lseq]
      have hprod : ((Pseq (φ n)).roots.map (fun r => x - r)).prod =
          ∏ i : Fin d, (x - zseq (φ n) i) := by
        rw [← hms, Multiset.map_map]
        exact (Finset.prod_eq_multiset_prod Finset.univ
          (fun i : Fin d => x - zseq (φ n) i)).symm
      rw [Polynomial.Splits.eval_eq_prod_roots_of_monic
        (IsAlgClosed.splits (Pseq (φ n))) (hmonicP (φ n)) x]
      exact hprod.symm
    exact tendsto_nhds_unique_of_eventuallyEq hlim2 hlim1
      (Eventually.of_forall heqseq)
  have hrootPoly_prod : rootPoly d w =
      (Multiset.map (fun a : ℂ => Polynomial.X - Polynomial.C a)
        (List.ofFn w : Multiset ℂ)).prod := by
    rw [rootPoly, Finset.prod_eq_multiset_prod]
    change (Multiset.map ((fun a : ℂ => Polynomial.X - Polynomial.C a) ∘ w)
      Finset.univ.val).prod = _
    rw [← Multiset.map_map, Fin.univ_val_map]
  have hwroots : P0.roots = (List.ofFn w : Multiset ℂ) := by
    rw [← hrootPoly_eq, hrootPoly_prod, Polynomial.roots_multiset_prod_X_sub_C]
  have hcountP : ∀ n, ((Pseq n).roots.filter (fun z => dist z α < ε)).card =
      (Finset.univ.filter (fun i : Fin d => dist (zseq n i) α < ε)).card := by
    intro n
    have hms : Multiset.map (zseq n) Finset.univ.val = (Pseq n).roots := by
      rw [Fin.univ_val_map, hofn]
      simp [lseq]
    have hleft : ((Pseq n).roots.filter (fun z => dist z α < ε)).card =
        (Pseq n).roots.countP (fun z => dist z α < ε) :=
      (Multiset.countP_eq_card_filter (fun z => dist z α < ε) (Pseq n).roots).symm
    rw [hleft]
    rw [← hms, Multiset.countP_map]
    rfl
  have hcount0 : P0.roots.count α =
      (Finset.univ.filter (fun i : Fin d => w i = α)).card := by
    rw [hwroots, ← Fin.univ_val_map w, Multiset.count_map]
    change (Finset.univ.val.filter (fun i : Fin d => α = w i)).card =
      (Finset.univ.val.filter (fun i : Fin d => w i = α)).card
    simp [eq_comm]
  have hwroot : ∀ i : Fin d, P0.IsRoot (w i) := by
    intro i
    apply Polynomial.isRoot_of_mem_roots
    rw [hwroots]
    simp
  have hevent_mem : ∀ᶠ n in atTop, ∀ i : Fin d,
      (dist (zseq (φ n) i) α < ε ↔ w i = α) := by
    rw [Filter.eventually_all]
    intro i
    have hwi_tend : Tendsto (fun n => zseq (φ n) i) atTop (nhds (w i)) :=
      hφtend.apply_nhds i
    by_cases hwi : w i = α
    · rw [hwi] at hwi_tend ⊢
      rw [Metric.tendsto_atTop] at hwi_tend
      obtain ⟨N, hN⟩ := hwi_tend ε hε
      filter_upwards [eventually_ge_atTop N] with n hn
      constructor
      · intro _; rfl
      · intro _; exact hN n hn
    · have hwifin : w i ∈ P0.roots.toFinset := by
        rw [hwroots]
        simp
      have hsep' : 2 * ε ≤ dist (w i) α := hsep (w i) hwifin hwi
      rw [Metric.tendsto_atTop] at hwi_tend
      obtain ⟨N, hN⟩ := hwi_tend ε hε
      filter_upwards [eventually_ge_atTop N] with n hn
      constructor
      · intro hlt
        have hnlt : dist (zseq (φ n) i) (w i) < ε := hN n hn
        have htri : dist (w i) α ≤ dist (w i) (zseq (φ n) i) +
            dist (zseq (φ n) i) α := dist_triangle _ _ _
        rw [dist_comm (w i) (zseq (φ n) i)] at htri
        nlinarith
      · intro hwia
        exact (hwi hwia).elim
  have hevent_count : ∀ᶠ n in atTop,
      (Finset.univ.filter (fun i : Fin d => dist (zseq (φ n) i) α < ε)).card =
      (Finset.univ.filter (fun i : Fin d => w i = α)).card := by
    filter_upwards [hevent_mem] with n hn
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i hi
    exact hn i
  have hevent_good : ∀ᶠ n in atTop,
      ((Pseq (φ n)).roots.filter (fun z => dist z α < ε)).card = P0.roots.count α := by
    filter_upwards [hevent_count] with n hn
    rw [hcountP (φ n), hcount0, hn]
  have hevent_bad : ∀ᶠ n in atTop,
      ((Pseq (φ n)).roots.filter (fun z => dist z α < ε)).card ≠ P0.roots.count α :=
    Eventually.of_forall (fun n => hbadP (φ n))
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hevent_good, hevent_bad] with n hgood hbadn
    exact hbadn hgood
  rcases hfalse.exists with ⟨n, hn⟩
  exact hn

/-- Simultaneous persistence of all distinct roots: for every root of $P_0$,
    every sufficiently close monic polynomial of the same degree has a nearby
    root. -/
theorem roots_persist_near_of_coeff_close
    (P0 : Polynomial ℂ) (hmonic0 : P0.Monic) (hd0 : 0 < P0.natDegree)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ P : Polynomial ℂ, P.Monic → P.natDegree = P0.natDegree →
      (∀ k ≤ P0.natDegree, ‖P.coeff k - P0.coeff k‖ < δ) →
      ∀ z ∈ P0.roots.toFinset, ∃ w : ℂ, P.IsRoot w ∧ dist w z < ε := by
  classical
  let S := P0.roots.toFinset
  have hsingle : ∀ z ∈ S, ∃ δ > 0, ∀ P : Polynomial ℂ, P.Monic →
      P.natDegree = P0.natDegree →
      (∀ k ≤ P0.natDegree, ‖P.coeff k - P0.coeff k‖ < δ) →
      ∃ w : ℂ, P.IsRoot w ∧ dist w z < ε := by
    intro z hz
    have hz' : z ∈ P0.roots.toFinset := by simpa only [S] using hz
    have hzm : z ∈ P0.roots := Multiset.mem_toFinset.mp hz'
    exact exists_root_near_of_coeff_close P0 hmonic0 hd0 z
      (Polynomial.isRoot_of_mem_roots hzm) ε hε
  let Good : Finset ℂ → Prop := fun t =>
    ∃ δ > 0, ∀ P : Polynomial ℂ, P.Monic → P.natDegree = P0.natDegree →
      (∀ k ≤ P0.natDegree, ‖P.coeff k - P0.coeff k‖ < δ) →
      ∀ z ∈ t, ∃ w : ℂ, P.IsRoot w ∧ dist w z < ε
  have hall_subset : ∀ t : Finset ℂ, t ⊆ S → Good t := by
    intro t
    refine Finset.induction_on t ?base ?step
    · intro hsub
      refine ⟨1, zero_lt_one, ?_⟩
      intro P hPm hPd hclose z hz
      simp at hz
    · intro a t hat ih hsub
      have haS : a ∈ S := hsub (by simp [hat])
      have htS : t ⊆ S := fun x hx => hsub (by simp [hx])
      rcases ih htS with ⟨δ, hδpos, hδprop⟩
      rcases hsingle a haS with ⟨δa, hδapos, hδaprop⟩
      refine ⟨min δ δa, lt_min hδpos hδapos, ?_⟩
      intro P hPm hPd hclose z hz
      rw [Finset.mem_insert] at hz
      rcases hz with hza | hzt
      · subst hza
        exact hδaprop P hPm hPd (fun k hk =>
          lt_of_lt_of_le (hclose k hk) (min_le_right _ _))
      · exact hδprop P hPm hPd (fun k hk =>
          lt_of_lt_of_le (hclose k hk) (min_le_left _ _)) z hzt
  exact hall_subset S (fun _ hx => hx)

end CollinsCAD
