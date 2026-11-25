import Mathlib
import Cslib
import NewtonRaphsonCC.Iteration
import NewtonRaphsonCC.Correctness
import NewtonRaphsonCC.Convergence
import NewtonRaphsonCC.Complexity

/-!
# Parameterized cost of arithmetic in the Newton iteration

The estimates in `Complexity.lean` charge one tick per Newton step, treating
arithmetic as free. We now replace that assumption with an explicit cost
parameter: a step whose operands have at most $b=\lfloor\log_2 n\rfloor$ bits
costs $D(b)$ ticks, where $D:\mathbb N\to\mathbb N$ is an arbitrary function.
Every iterate is bounded by the input $n$, so charging $D(b)$ at every step is
an upper bound without any monotonicity hypothesis on $D$.

The results are therefore **conditional**: they describe the algorithm's cost
relative to the assumed division cost, not a measured or implementation-proved
running time. A multiplication cost $M(b)$ can be introduced later as a separate
hypothesis $D(b)=O(M(b))$; it is not needed for the Heron step itself, which
uses division, addition and a halving.
-/

namespace NewtonRaphsonCC

open Cslib.Algorithms.Lean

/-- The Newton loop with the arithmetic of each step charged at $D(b)$ ticks.

The control flow is identical to `newtonLoop`; only the tick weight differs.
The parameter $b=\lfloor\log_2 n\rfloor$ is fixed for the whole run, so it is an
upper bound on the bit length of every iterate. -/
def weightedLoop (D : ℕ → ℕ) (b n x : ℕ) : TimeM ℕ ℕ :=
  TimeM.tick (D b) >>= fun _ =>
    if newtonStep n x < x then
      weightedLoop D b n (newtonStep n x)
    else
      pure x
termination_by x

/-- Integer square root under the parameterized cost model.

The seed is the same power of two as for `seededSqrt`, and the cost parameter is
$D(\lfloor\log_2 n\rfloor)$; the case $n=0$ performs no arithmetic. -/
def weightedSqrt (D : ℕ → ℕ) (n : ℕ) : TimeM ℕ ℕ :=
  if n = 0 then
    pure 0
  else
    weightedLoop D (Nat.log 2 n) n (newtonSeed n)

/-- Recurrence for the return value of the weighted loop.

The extra tick does not affect the value, so the recurrence is the same as for
`newtonLoop`. -/
theorem weightedLoop_ret (D : ℕ → ℕ) (b n x : ℕ) :
    (weightedLoop D b n x).ret =
      if newtonStep n x < x then (weightedLoop D b n (newtonStep n x)).ret else x := by
  by_cases h : newtonStep n x < x
  · rw [weightedLoop]; simp [h]
  · rw [weightedLoop]; simp [h]

/-- Recurrence for the weighted tick count: each iteration contributes $D(b)$,
and only a decreasing step recurses. -/
theorem weightedLoop_time (D : ℕ → ℕ) (b n x : ℕ) :
    (weightedLoop D b n x).time =
      D b + if newtonStep n x < x then (weightedLoop D b n (newtonStep n x)).time else 0 := by
  by_cases h : newtonStep n x < x
  · rw [weightedLoop]; simp [h, TimeM.time_tick]
  · rw [weightedLoop]; simp [h, TimeM.time_tick]

/-- The weighted loop returns exactly the same value as the unit-cost loop.

By induction on the iterate, the two recurrences differ only in their tick
weight, not in their control flow. -/
theorem weightedLoop_ret_eq_newtonLoop (D : ℕ → ℕ) (b n x : ℕ) :
    (weightedLoop D b n x).ret = (newtonLoop n x).ret := by
  induction x using Nat.strong_induction_on with
  | ind x ih =>
    rw [weightedLoop_ret, newtonLoop_ret]
    split_ifs with h
    · exact ih (newtonStep n x) h
    · rfl

/-- The weighted tick count is the unit-cost iteration count multiplied by $D(b)$:
\[
\operatorname{time}_D(\operatorname{weightedLoop}(D,b,n,x))
  = D(b)\cdot\operatorname{time}(\operatorname{newtonLoop}(n,x)).
\]
This is the algebraic core of the parameterization. -/
theorem weightedLoop_time_eq_mul (D : ℕ → ℕ) (b n x : ℕ) :
    (weightedLoop D b n x).time = D b * (newtonLoop n x).time := by
  induction x using Nat.strong_induction_on with
  | ind x ih =>
    rw [weightedLoop_time, newtonLoop_time]
    by_cases h : newtonStep n x < x
    · simp [h, ih (newtonStep n x) h]
      ring
    · simp [h]

/-- Correctness under the parameterized cost model: the weighted program still
returns $\lfloor\sqrt n\rfloor$, since its control flow agrees with `seededSqrt`. -/
theorem weightedSqrt_correct (D : ℕ → ℕ) (n : ℕ) :
    (weightedSqrt D n).ret = n.sqrt := by
  unfold weightedSqrt
  split_ifs with h0
  · subst h0; simp
  · rw [weightedLoop_ret_eq_newtonLoop]
    exact newtonLoop_ret_eq_sqrt n (newtonSeed n)
      (Nat.pos_of_ne_zero h0) (sqrt_le_newtonSeed n)

/-- Conditional complexity bound:
\[
\operatorname{time}_D(\operatorname{weightedSqrt}(D,n))
  \le D(\lfloor\log_2 n\rfloor)
     \Bigl(\bigl\lfloor\log_2(\lfloor\log_2 n\rfloor+2)\bigr\rfloor+3\Bigr).
\]
The factor in parentheses is the O(log log n) iteration bound already proved
for the seeded algorithm. -/
theorem weightedSqrt_time_le (D : ℕ → ℕ) (n : ℕ) :
    (weightedSqrt D n).time ≤
      D (Nat.log 2 n) * (Nat.log 2 (Nat.log 2 n + 2) + 3) := by
  unfold weightedSqrt
  split_ifs with h0
  · simp
  · rw [weightedLoop_time_eq_mul]
    have hs : (newtonLoop n (newtonSeed n)).time = (seededSqrt n).time := by
      simp [seededSqrt, h0]
    rw [hs]
    exact Nat.mul_le_mul_left _ (seededSqrt_time_le n)

end NewtonRaphsonCC
