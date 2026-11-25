import Mathlib
import Cslib

/-!
# Timed Newton–Raphson iteration for $\lfloor\sqrt n\rfloor$

We define the integer Heron map and place it inside CSLib's `TimeM` cost monad.
The cost model is unit-cost iteration count: one tick is charged per Newton
step, while the termination test and arithmetic on $\mathbb N$ are free. Thus
`TimeM.time` is an annotated count, not a measured runtime, and every bound
proved below refers to this model.
-/

namespace NewtonRaphsonCC

open Cslib.Algorithms.Lean

/--
The integer Heron map $x\mapsto\left\lfloor\frac{x+\lfloor n/x\rfloor}{2}\right\rfloor$.

For $x>0$ this map fixes $s=\lfloor\sqrt n\rfloor$ and strictly decreases for
$x>s$; both assertions are proved in the files that follow.
-/
def newtonStep (n x : ℕ) : ℕ :=
  (x + n / x) / 2

/--
The iteration begun at $x$, charging one tick per Newton step.

The recursion is well founded: it calls itself only when the new iterate is
strictly smaller, $x_{k+1}<x_k$.
-/
def newtonLoop (n x : ℕ) : TimeM ℕ ℕ := do
  ✓ let y := newtonStep n x
  if y < x then
    newtonLoop n y
  else
    pure x
termination_by x

/--
Integer square root by Heron iteration from the naive seed $x_0=n$.

The case $n=0$ returns $0$ at once; for $n>0$ the orbit starts at $n$.
-/
def newtonSqrt (n : ℕ) : TimeM ℕ ℕ :=
  if n = 0 then
    pure 0
  else
    newtonLoop n n

/--
Recurrence for the return value of one loop step:
\[
\operatorname{ret}(\operatorname{newtonLoop}(n,x))=
\begin{cases}
\operatorname{ret}(\operatorname{newtonLoop}(n,\operatorname{newtonStep}(n,x))),
  & \operatorname{newtonStep}(n,x)<x,\\
x, & \text{otherwise.}
\end{cases}
\]
-/
theorem newtonLoop_ret (n x : ℕ) :
    (newtonLoop n x).ret =
      if newtonStep n x < x then (newtonLoop n (newtonStep n x)).ret else x := by
  by_cases h : newtonStep n x < x
  · rw [newtonLoop]; simp [h]
  · rw [newtonLoop]; simp [h]

/--
Recurrence for the tick count of one loop step:
\[
\operatorname{time}(\operatorname{newtonLoop}(n,x))=
1+\begin{cases}
\operatorname{time}(\operatorname{newtonLoop}(n,\operatorname{newtonStep}(n,x))),
  & \operatorname{newtonStep}(n,x)<x,\\
0, & \text{otherwise.}
\end{cases}
\]
Every call costs one tick; only a decreasing step recurses.
-/
theorem newtonLoop_time (n x : ℕ) :
    (newtonLoop n x).time =
      1 + if newtonStep n x < x then (newtonLoop n (newtonStep n x)).time else 0 := by
  by_cases h : newtonStep n x < x
  · rw [newtonLoop]; simp [h]
  · rw [newtonLoop]; simp [h]

/--
The power-of-two seed $x_0=2^{\lfloor\log_2 n\rfloor/2+1}$, equal to
$2^{\lceil\operatorname{bitlength}(n)/2\rceil}$ for $n\geq 1$. It lies within a
factor $2$ of $\lfloor\sqrt n\rfloor$, so the initial overshoot is bounded.
-/
def newtonSeed (n : ℕ) : ℕ :=
  2 ^ (Nat.log 2 n / 2 + 1)

/--
Integer square root by Heron iteration from the power-of-two seed.

The cost model is the same as for `newtonSqrt`: one tick per loop iteration,
with the computation of the seed free. The case $n=0$ returns immediately.
-/
def seededSqrt (n : ℕ) : TimeM ℕ ℕ :=
  if n = 0 then
    pure 0
  else
    newtonLoop n (newtonSeed n)

end NewtonRaphsonCC
