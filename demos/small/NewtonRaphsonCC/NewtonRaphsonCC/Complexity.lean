import Mathlib
import Cslib
import NewtonRaphsonCC.Iteration
import NewtonRaphsonCC.Convergence

/-!
# Asymptotic complexity of Newton–Raphson integer square root

Following CSLib's `mergeSort_time` pattern, we first record explicit bounds
$g(n)$ on the annotated tick count, then show in Mathlib's `Asymptotics.IsBigO`
sense that $g(n)=O(\log n)$ for the naive seed and $g(n)=O(\log\log n)$ for the
power-of-two seed. Only this file passes to $\mathbb R$; the algorithms and
their convergence estimates remain in $\mathbb N$.
-/

namespace NewtonRaphsonCC

open Filter Asymptotics

/--
Explicit upper bound $g(n)=\lfloor\log_2 n\rfloor+2$ on
$\operatorname{time}(\operatorname{newtonSqrt}(n))$.
-/
def newtonSqrtBound (n : ℕ) : ℕ :=
  Nat.log 2 n + 2

/--
Explicit complexity estimate
$\operatorname{time}(\operatorname{newtonSqrt}(n))\leq g(n)$, in the style of
CSLib's `mergeSort_time`; the $O(\log n)$ form is derived below.
-/
theorem newtonSqrt_time (n : ℕ) :
    (newtonSqrt n).time ≤ newtonSqrtBound n :=
  newtonSqrt_time_le n

/--
Bridge between discrete and continuous logarithms:
\[
(\lfloor\log_2 n\rfloor:\mathbb R)\leq\frac{\log n}{\log 2}\qquad(n\geq 1).
\]
From $2^{\lfloor\log_2 n\rfloor}\leq n$, monotonicity of $\log$ and
$\log(x^k)=k\log x$ give $(\lfloor\log_2 n\rfloor)\log 2\leq\log n$.
-/
theorem nat_log2_cast_le (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2_pos]
  have hpow_nat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hpow : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast hpow_nat
  have hlog := Real.log_le_log (by positivity) hpow
  rwa [Real.log_pow] at hlog

/--
The explicit bound is $O(\log n)$ at $+\infty$:
\[
g=O(\log n),\qquad g(n)=\lfloor\log_2 n\rfloor+2 .
\]
For $n\geq 2$ one has $\log 2\leq\log n$, hence
$g(n)\leq(3/\log 2)\log n$.
-/
theorem newtonSqrtBound_isBigO :
    (fun n : ℕ => (newtonSqrtBound n : ℝ)) =O[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨3 / Real.log 2, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog_ge : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) h2n
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := le_trans hlog2_pos.le hlog_ge
  have hcast : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
    nat_log2_cast_le n (by omega)
  have h2_le : (2 : ℝ) ≤ 2 * (Real.log (n : ℝ) / Real.log 2) := by
    have h1 : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
      (one_le_div hlog2_pos).mpr hlog_ge
    linarith
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hlog_nonneg]
  unfold newtonSqrtBound
  push_cast
  have hdiv : 3 / Real.log 2 * Real.log (n : ℝ) =
      3 * (Real.log (n : ℝ) / Real.log 2) := by
    ring
  linarith

/--
Asymptotic complexity of the naive-seed algorithm:
\[
\bigl(\operatorname{time}(\operatorname{newtonSqrt}(n)):\mathbb R\bigr)
  =O(\log n)\quad(n\to\infty).
\]
The tick count is bounded by $g$ pointwise and $g=O(\log n)$.
-/
theorem newtonSqrt_time_isBigO :
    (fun n : ℕ => ((newtonSqrt n).time : ℝ)) =O[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  have hle : (fun n : ℕ => ((newtonSqrt n).time : ℝ)) =O[atTop]
      (fun n : ℕ => (newtonSqrtBound n : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards with n
    rw [one_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast newtonSqrt_time n
  exact hle.trans newtonSqrtBound_isBigO

/--
Explicit upper bound
$g(n)=\left\lfloor\log_2(\lfloor\log_2 n\rfloor+2)\right\rfloor+3$ on
$\operatorname{time}(\operatorname{seededSqrt}(n))$.
-/
def seededSqrtBound (n : ℕ) : ℕ :=
  Nat.log 2 (Nat.log 2 n + 2) + 3

/--
Explicit complexity estimate
$\operatorname{time}(\operatorname{seededSqrt}(n))\leq g(n)$.
-/
theorem seededSqrt_time (n : ℕ) :
    (seededSqrt n).time ≤ seededSqrtBound n :=
  seededSqrt_time_le n

/--
Domain guard for iterated logarithms: for $n\geq 9$,
\[
2\leq\log n\qquad\text{and}\qquad \log 2\leq\log(\log n).
\]
Since $e<3$, we have $e^2<9\leq n$, and monotonicity of $\log$ applies twice.
-/
theorem log_two_le_log_log_of_ge_nine (n : ℕ) (hn : 9 ≤ n) :
    2 ≤ Real.log (n : ℝ) ∧ Real.log 2 ≤ Real.log (Real.log (n : ℝ)) := by
  have hexp2 : Real.exp 2 < (n : ℝ) := by
    have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hpos : 0 < Real.exp 1 := Real.exp_pos 1
    have h9 : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hlog_ge : 2 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 2) hexp2.le
    rwa [Real.log_exp] at h
  have hloglog_ge : Real.log 2 ≤ Real.log (Real.log (n : ℝ)) :=
    Real.log_le_log (by norm_num) hlog_ge
  exact ⟨hlog_ge, hloglog_ge⟩

/--
The explicit bound is $O(\log\log n)$ at $+\infty$:
\[
g(n)=\left\lfloor\log_2(\lfloor\log_2 n\rfloor+2)\right\rfloor+3
  =O(\log(\log n)).
\]
For $n\geq9$ the inner logarithm is bounded by a multiple of $\log n$, and a
second application of the bridge lemma controls the outer logarithm by
$2+\log(\log n)/\log 2$.
-/
theorem seededSqrtBound_isBigO :
    (fun n : ℕ => (seededSqrtBound n : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (Real.log (n : ℝ))) := by
  rw [isBigO_iff]
  refine ⟨6 / Real.log 2, ?_⟩
  filter_upwards [eventually_ge_atTop 9] with n hn
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  obtain ⟨hlog_ge, hloglog_ge⟩ := log_two_le_log_log_of_ge_nine n hn
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) :=
    le_trans hlog2_pos.le hloglog_ge
  have hnat_log : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have h1 := nat_log2_cast_le n (by omega)
    have h2 : Real.log (n : ℝ) / Real.log 2 ≤ 2 * Real.log (n : ℝ) := by
      rw [div_le_iff₀ hlog2_pos]
      nlinarith
    exact le_trans h1 h2
  have hinner : ((Nat.log 2 n + 2 : ℕ) : ℝ) ≤ 4 * Real.log (n : ℝ) := by
    push_cast
    linarith
  have houter : (Nat.log 2 (Nat.log 2 n + 2) : ℝ) ≤
      2 + Real.log (Real.log (n : ℝ)) / Real.log 2 := by
    have h1 := nat_log2_cast_le (Nat.log 2 n + 2) (by omega)
    have h2 : Real.log ((Nat.log 2 n + 2 : ℕ) : ℝ) ≤
        Real.log (4 * Real.log (n : ℝ)) :=
      Real.log_le_log (by positivity) hinner
    have h3 : Real.log (4 * Real.log (n : ℝ)) =
        2 * Real.log 2 + Real.log (Real.log (n : ℝ)) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hlog_pos)]
      have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
        norm_num
      linarith
    have h4 : Real.log ((Nat.log 2 n + 2 : ℕ) : ℝ) / Real.log 2 ≤
        (2 * Real.log 2 + Real.log (Real.log (n : ℝ))) / Real.log 2 :=
      div_le_div_of_nonneg_right (h3 ▸ h2) hlog2_pos.le
    have h5 : (2 * Real.log 2 + Real.log (Real.log (n : ℝ))) / Real.log 2 =
        2 + Real.log (Real.log (n : ℝ)) / Real.log 2 := by
      field_simp
    linarith
  have hone : (1 : ℝ) ≤ Real.log (Real.log (n : ℝ)) / Real.log 2 :=
    (one_le_div hlog2_pos).mpr hloglog_ge
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hloglog_nonneg]
  unfold seededSqrtBound
  push_cast
  have hdiv : 6 / Real.log 2 * Real.log (Real.log (n : ℝ)) =
      6 * (Real.log (Real.log (n : ℝ)) / Real.log 2) := by
    ring
  linarith

/--
Asymptotic complexity of the seeded algorithm:
\[
\bigl(\operatorname{time}(\operatorname{seededSqrt}(n)):\mathbb R\bigr)
  =O(\log(\log n))\quad(n\to\infty).
\]
Composed from the explicit bound and its asymptotic class.
-/
theorem seededSqrt_time_isBigO :
    (fun n : ℕ => ((seededSqrt n).time : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (Real.log (n : ℝ))) := by
  have hle : (fun n : ℕ => ((seededSqrt n).time : ℝ)) =O[atTop]
      (fun n : ℕ => (seededSqrtBound n : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards with n
    rw [one_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast seededSqrt_time n
  exact hle.trans seededSqrtBound_isBigO

end NewtonRaphsonCC
