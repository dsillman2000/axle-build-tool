import Mathlib
import Cslib
import NewtonRaphsonCC.Iteration

/-!
# Correctness of the integer Newton–Raphson square root

Write $s=\lfloor\sqrt n\rfloor$. We prove $\operatorname{ret}(\operatorname{newtonSqrt}(n))=s$
from two invariants: a Newton step from a positive $x$ never drops below $s$,
and a point with $x\leq\operatorname{newtonStep}(n,x)$ already satisfies
$x\leq s$. Strong induction on the iterate then closes the argument.
-/

namespace NewtonRaphsonCC

/--
A Newton step from a positive $x$ never undershoots $s=\lfloor\sqrt n\rfloor$:
\[
s\leq\left\lfloor\frac{x+\lfloor n/x\rfloor}{2}\right\rfloor .
\]
Split on $x<2s$: in that case $(2s-x)x\leq s^2\leq n$ gives $2s-x\leq n/x$;
otherwise $x+\lfloor n/x\rfloor\geq 2s$ directly.
-/
theorem sqrt_le_newtonStep (n x : ℕ) (hx : 0 < x) :
    n.sqrt ≤ newtonStep n x := by
  unfold newtonStep
  suffices h : 2 * n.sqrt ≤ x + n / x by omega
  by_cases hlt : x < 2 * n.sqrt
  · have hxle : x ≤ 2 * n.sqrt := Nat.le_of_lt hlt
    have hdiv : 2 * n.sqrt - x ≤ n / x := by
      rw [Nat.le_div_iff_mul_le hx]
      have hsq_int : ((n.sqrt : ℤ) * (n.sqrt : ℤ)) ≤ (n : ℤ) := by
        exact_mod_cast Nat.sqrt_le n
      have hprod_int : (((2 * n.sqrt - x : ℕ) : ℤ) * (x : ℤ)) ≤ (n : ℤ) := by
        rw [Nat.cast_sub hxle]
        push_cast
        nlinarith [sq_nonneg ((n.sqrt : ℤ) - (x : ℤ))]
      exact_mod_cast hprod_int
    calc
      2 * n.sqrt = x + (2 * n.sqrt - x) := (Nat.add_sub_of_le hxle).symm
      _ ≤ x + n / x := Nat.add_le_add_left hdiv x
  · have hxge : 2 * n.sqrt ≤ x := Nat.le_of_not_gt hlt
    exact le_trans hxge (Nat.le_add_right x (n / x))

/--
A stopping point lies at or below the floor root.

If $x\leq\left\lfloor (x+\lfloor n/x\rfloor)/2\right\rfloor$ then
$x\leq n/x$, hence $x^2\leq n$, which is the characterization
$x\leq\lfloor\sqrt n\rfloor$.
-/
theorem le_sqrt_of_le_newtonStep (n x : ℕ) (hx : 0 < x) (h : x ≤ newtonStep n x) :
    x ≤ n.sqrt := by
  unfold newtonStep at h
  have hdiv : x ≤ n / x := by omega
  have hmul : x * x ≤ n := (Nat.le_div_iff_mul_le hx).mp hdiv
  exact Nat.le_sqrt.mpr hmul

/--
Every iterate starting at $x\geq s$ terminates at exactly $s=\lfloor\sqrt n\rfloor$.

Strong induction is on $x$: a strict step moves to a smaller iterate still
above $s$, while at a non-decreasing point the two invariant lemmas give
equality with $s$.
-/
theorem newtonLoop_ret_eq_sqrt (n x : ℕ) (hn : 0 < n) (hx : n.sqrt ≤ x) :
    (newtonLoop n x).ret = n.sqrt := by
  induction x using Nat.strong_induction_on with
  | ind x ih =>
    have hsqrt_pos : 0 < n.sqrt := Nat.le_sqrt.mpr (by omega)
    have hx_pos : 0 < x := lt_of_lt_of_le hsqrt_pos hx
    rw [newtonLoop_ret]
    split_ifs with hlt
    · exact ih (newtonStep n x) hlt (sqrt_le_newtonStep n x hx_pos)
    · exact le_antisymm (le_sqrt_of_le_newtonStep n x hx_pos (Nat.le_of_not_lt hlt)) hx

/--
Main correctness theorem:
\[
\operatorname{ret}(\operatorname{newtonSqrt}(n))=\lfloor\sqrt n\rfloor .
\]
For $n=0$ this is immediate; for $n>0$ the seed $n$ dominates $\lfloor\sqrt n\rfloor$,
so the loop invariant applies.
-/
theorem newtonSqrt_correct (n : ℕ) : (newtonSqrt n).ret = n.sqrt := by
  unfold newtonSqrt
  split_ifs with h0
  · subst h0; simp
  · exact newtonLoop_ret_eq_sqrt n n (Nat.pos_of_ne_zero h0) (Nat.sqrt_le_self n)

/--
The power-of-two seed is never below the floor root:
$s\leq 2^{\lfloor\log_2 n\rfloor/2+1}$.

Indeed $n<2^{\lfloor\log_2 n\rfloor+1}$ and
$\lfloor\log_2 n\rfloor+1\leq 2(\lfloor\log_2 n\rfloor/2+1)$, so
$n<\operatorname{newtonSeed}(n)^2$, and $s<m\iff n<m^2$ concludes.
-/
theorem sqrt_le_newtonSeed (n : ℕ) : n.sqrt ≤ newtonSeed n := by
  by_cases h0 : n = 0
  · subst h0; simp [newtonSeed]
  · have hlt : n < 2 ^ (Nat.log 2 n + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) n
    have hexp : Nat.log 2 n + 1 ≤ 2 * (Nat.log 2 n / 2 + 1) := by omega
    have hpow : 2 ^ (Nat.log 2 n + 1) ≤ newtonSeed n * newtonSeed n := by
      unfold newtonSeed
      calc
        2 ^ (Nat.log 2 n + 1)
            ≤ 2 ^ (2 * (Nat.log 2 n / 2 + 1)) := Nat.pow_le_pow_right (by norm_num) hexp
        _ = 2 ^ (Nat.log 2 n / 2 + 1) * 2 ^ (Nat.log 2 n / 2 + 1) := by
          rw [two_mul, pow_add]
    exact Nat.le_of_lt (Nat.sqrt_lt.mpr (lt_of_lt_of_le hlt hpow))

/--
For $n>0$ the seed overshoots $s=\lfloor\sqrt n\rfloor$ by at most a factor $2$:
\[
2^{\lfloor\log_2 n\rfloor/2+1}\leq 2s .
\]
Since $2^{\lfloor\log_2 n\rfloor/2}$ squares to at most $n$, it is at most $s$.
-/
theorem newtonSeed_le_two_mul_sqrt (n : ℕ) (hn : 0 < n) :
    newtonSeed n ≤ 2 * n.sqrt := by
  have hpow : 2 ^ (Nat.log 2 n / 2) * 2 ^ (Nat.log 2 n / 2) ≤ n := by
    calc
      2 ^ (Nat.log 2 n / 2) * 2 ^ (Nat.log 2 n / 2)
          = 2 ^ (2 * (Nat.log 2 n / 2)) := by rw [two_mul, pow_add]
      _ ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hle : 2 ^ (Nat.log 2 n / 2) ≤ n.sqrt := Nat.le_sqrt.mpr hpow
  unfold newtonSeed
  rw [pow_succ]
  omega

/--
Uniform seed estimate valid for every $n\in\mathbb N$:
\[
\operatorname{newtonSeed}(n)\leq 2\max(1,\lfloor\sqrt n\rfloor).
\]
The extra maximum covers the degenerate case $n=0$.
-/
theorem newtonSeed_le_two_mul_max_sqrt (n : ℕ) :
    newtonSeed n ≤ 2 * max 1 n.sqrt := by
  by_cases h0 : n = 0
  · subst h0; simp [newtonSeed]
  · have := newtonSeed_le_two_mul_sqrt n (Nat.pos_of_ne_zero h0)
    omega

/--
Functional correctness of the seeded square root:
$\operatorname{ret}(\operatorname{seededSqrt}(n))=\lfloor\sqrt n\rfloor$.

The seed satisfies the loop invariant $s\leq x_0$, so correctness follows from
the same strong-induction theorem as for the naive seed.
-/
theorem seededSqrt_correct (n : ℕ) : (seededSqrt n).ret = n.sqrt := by
  unfold seededSqrt
  split_ifs with h0
  · subst h0; simp
  · exact newtonLoop_ret_eq_sqrt n (newtonSeed n)
      (Nat.pos_of_ne_zero h0) (sqrt_le_newtonSeed n)

end NewtonRaphsonCC
