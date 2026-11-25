import Mathlib
import Cslib
import NewtonRaphsonCC.Iteration
import NewtonRaphsonCC.Correctness

/-!
# Explicit iteration bounds for Newton–Raphson

Above $s=\lfloor\sqrt n\rfloor$ we have $\lfloor n/x\rfloor\leq s$, so one
Newton step at least halves the overshoot $x-s$. This yields the bound
$\lfloor\log_2 n\rfloor+2$ from the naive seed $x_0=n$. A sharper shifted
invariant absorbs the floor-rounding term and gives quadratic decay, hence a
doubly logarithmic bound for the power-of-two seed.
-/

namespace NewtonRaphsonCC

/--
Above the floor root the quotient is bounded: if $s<x$ then $\lfloor n/x\rfloor\leq s$.

From $n<(s+1)^2\leq(s+1)x$ division by $x>0$ gives $n/x<s+1$.
-/
theorem div_le_sqrt_of_sqrt_lt (n x : ℕ) (h : n.sqrt < x) :
    n / x ≤ n.sqrt := by
  have hx : 0 < x := by omega
  have hlt : n < (n.sqrt + 1) * x := by
    have h1 : n < (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt n
    have h2 : (n.sqrt + 1) * (n.sqrt + 1) ≤ (n.sqrt + 1) * x :=
      Nat.mul_le_mul_left _ h
    exact lt_of_lt_of_le h1 h2
  have hdiv : n / x < n.sqrt + 1 := (Nat.div_lt_iff_lt_mul hx).mpr hlt
  omega

/--
One Newton step above the root at least halves the overshoot:
\[
\operatorname{newtonStep}(n,x)-s\leq\left\lfloor\frac{x-s}{2}\right\rfloor .
\]
It uses $\lfloor n/x\rfloor\leq s<x$ and elementary arithmetic in $\mathbb N$.
-/
theorem newtonStep_sub_sqrt_le (n x : ℕ) (h : n.sqrt < x) :
    newtonStep n x - n.sqrt ≤ (x - n.sqrt) / 2 := by
  have hdiv : n / x ≤ n.sqrt := div_le_sqrt_of_sqrt_lt n x h
  unfold newtonStep
  omega

/--
Explicit tick bound in terms of the initial overshoot:
\[
\operatorname{time}(\operatorname{newtonLoop}(n,x))
  \leq\lfloor\log_2(x-s)\rfloor+2 .
\]
By strong induction a strict step costs one tick and sends $d=x-s$ to at most
$\lfloor d/2\rfloor$, so the bound follows from $2^{\lfloor\log_2 d\rfloor}\leq d$.
-/
theorem newtonLoop_time_le (n x : ℕ) (hn : 0 < n) (hx : n.sqrt ≤ x) :
    (newtonLoop n x).time ≤ Nat.log 2 (x - n.sqrt) + 2 := by
  induction x using Nat.strong_induction_on with
  | ind x ih =>
    have hsqrt_pos : 0 < n.sqrt := Nat.le_sqrt.mpr (by omega)
    have hx_pos : 0 < x := lt_of_lt_of_le hsqrt_pos hx
    rw [newtonLoop_time]
    split_ifs with hlt
    · have hgt : n.sqrt < x := by
        by_contra hle
        have heq : x = n.sqrt := by omega
        have hstep := sqrt_le_newtonStep n x hx_pos
        omega
      set y := newtonStep n x
      have hy_ge : n.sqrt ≤ y := sqrt_le_newtonStep n x hx_pos
      have hhalf : y - n.sqrt ≤ (x - n.sqrt) / 2 := newtonStep_sub_sqrt_le n x hgt
      by_cases hy0 : y - n.sqrt = 0
      · have hyeq : y = n.sqrt := by omega
        have hy_time : (newtonLoop n y).time = 1 := by
          rw [newtonLoop_time]
          by_cases hstep_lt : newtonStep n y < y
          · have hstep := sqrt_le_newtonStep n y (by omega)
            omega
          · simp [hstep_lt]
        omega
      · have hih := ih y hlt hy_ge
        have hlog : Nat.log 2 (y - n.sqrt) + 1 ≤ Nat.log 2 (x - n.sqrt) := by
          apply Nat.le_log_of_pow_le (by norm_num)
          have hpow : 2 ^ Nat.log 2 (y - n.sqrt) ≤ y - n.sqrt :=
            Nat.pow_log_le_self 2 hy0
          have hdouble : 2 ^ (Nat.log 2 (y - n.sqrt) + 1) =
              2 * 2 ^ Nat.log 2 (y - n.sqrt) := by
            ring
          omega
        omega
    · omega

/--
Explicit tick bound from the naive seed $x_0=n$:
\[
\operatorname{time}(\operatorname{newtonSqrt}(n))\leq\lfloor\log_2 n\rfloor+2 .
\]
Since $n-s\leq n$ and $\lfloor\log_2\cdot\rfloor$ is monotone, the previous
bound specializes to this form.
-/
theorem newtonSqrt_time_le (n : ℕ) :
    (newtonSqrt n).time ≤ Nat.log 2 n + 2 := by
  unfold newtonSqrt
  split_ifs with h0
  · simp
  · have h1 := newtonLoop_time_le n n (Nat.pos_of_ne_zero h0) (Nat.sqrt_le_self n)
    have h2 : Nat.log 2 (n - n.sqrt) ≤ Nat.log 2 n :=
      Nat.log_mono_right (Nat.sub_le n n.sqrt)
    omega

/--
Pure-$\mathbb N$ quadratic decay of the shifted overshoot.

Writing $s=\lfloor\sqrt n\rfloor$, $e=x-s-1$ and
$e'=\operatorname{newtonStep}(n,x)-s-1$, the rounding term $n\leq s^2+2s$ is
absorbed by the shift, yielding
\[
2s\,e'\leq e^2 .
\]
This is the engine of the doubly logarithmic iteration bound.
-/
theorem newtonStep_quadratic (n x : ℕ) (h : n.sqrt < x) :
    2 * n.sqrt * (newtonStep n x - n.sqrt - 1) ≤ (x - n.sqrt - 1) ^ 2 := by
  by_cases hy : newtonStep n x ≤ n.sqrt + 1
  · have hzero : newtonStep n x - n.sqrt - 1 = 0 := by omega
    rw [hzero, mul_zero]
    exact Nat.zero_le _
  · set s := n.sqrt
    set y := newtonStep n x
    set e := x - s - 1
    set e' := y - s - 1
    have hx_eq : x = s + 1 + e := by omega
    have hy_eq : y = s + 1 + e' := by omega
    have h2y : 2 * y ≤ x + n / x := Nat.mul_div_le (x + n / x) 2
    have hdiv : x * (n / x) ≤ n := Nat.mul_div_le n x
    have h2xy : 2 * x * y ≤ x * x + n := by nlinarith
    have hn : n ≤ s * s + 2 * s := by
      have := Nat.lt_succ_sqrt n
      nlinarith
    have hcomb : 2 * (s + 1 + e) * (s + 1 + e') ≤
        (s + 1 + e) * (s + 1 + e) + s * s + 2 * s := by
      rw [← hx_eq, ← hy_eq]
      omega
    nlinarith

/--
Endgame estimate: for $n>0$ and $s\leq x\leq s+1$,
\[
\operatorname{time}(\operatorname{newtonLoop}(n,x))\leq 2 .
\]
At $s+1$ one step reaches $s$, and at $s$ the loop stops after a single tick.
-/
theorem newtonLoop_time_le_two_of_le_succ (n x : ℕ) (hn : 0 < n)
    (hx : n.sqrt ≤ x) (hx1 : x ≤ n.sqrt + 1) :
    (newtonLoop n x).time ≤ 2 := by
  have hsqrt_pos : 0 < n.sqrt := Nat.le_sqrt.mpr (by omega)
  rw [newtonLoop_time]
  split_ifs with hlt
  · have hgt : n.sqrt < x := by
      by_contra hle
      have hstep := sqrt_le_newtonStep n x (by omega)
      omega
    have hsub : newtonStep n x - n.sqrt ≤ (x - n.sqrt) / 2 :=
      newtonStep_sub_sqrt_le n x hgt
    have hy_ge : n.sqrt ≤ newtonStep n x := sqrt_le_newtonStep n x (by omega)
    have hy_eq : newtonStep n x = n.sqrt := by omega
    rw [hy_eq, newtonLoop_time]
    have hnot : ¬ newtonStep n n.sqrt < n.sqrt := by
      have hstep := sqrt_le_newtonStep n n.sqrt hsqrt_pos
      omega
    simp [hnot]
  · omega

/--
Doubling induction for the quadratic phase.

If $1\leq p$, $2^{p-1}(x-s-1)\leq s$ and $s<2^{2^k p-1}$, then
\[
\operatorname{time}(\operatorname{newtonLoop}(n,x))\leq k+2 .
\]
Each Newton step replaces $p$ by $2p$; once $2^{p-1}>s$ the endgame estimate applies.
-/
theorem newtonLoop_time_le_of_pow_mul_le (n : ℕ) (hn : 0 < n) :
    ∀ k x p : ℕ, n.sqrt ≤ x → 1 ≤ p →
      2 ^ (p - 1) * (x - n.sqrt - 1) ≤ n.sqrt →
      n.sqrt < 2 ^ (2 ^ k * p - 1) →
      (newtonLoop n x).time ≤ k + 2
  | 0, x, p, hx, _, hinv, hk => by
    have hk' : n.sqrt < 2 ^ (p - 1) := by simpa using hk
    have hx1 : x ≤ n.sqrt + 1 := by
      by_contra hgt
      have hpos : 1 ≤ x - n.sqrt - 1 := by omega
      have : 2 ^ (p - 1) ≤ 2 ^ (p - 1) * (x - n.sqrt - 1) :=
        Nat.le_mul_of_pos_right _ hpos
      omega
    exact newtonLoop_time_le_two_of_le_succ n x hn hx hx1
  | k + 1, x, p, hx, hp, hinv, hk => by
    have hsqrt_pos : 0 < n.sqrt := Nat.le_sqrt.mpr (by omega)
    rw [newtonLoop_time]
    split_ifs with hlt
    · have hgt : n.sqrt < x := by
        by_contra hle
        have hstep := sqrt_le_newtonStep n x (by omega)
        omega
      set y := newtonStep n x
      have hy_ge : n.sqrt ≤ y := sqrt_le_newtonStep n x (by omega)
      have hquad : 2 * n.sqrt * (y - n.sqrt - 1) ≤ (x - n.sqrt - 1) ^ 2 :=
        newtonStep_quadratic n x hgt
      have hpow_eq : 2 ^ (2 * p - 1) = 2 * (2 ^ (p - 1)) ^ 2 := by
        have hexp : 2 * p - 1 = 1 + ((p - 1) + (p - 1)) := by omega
        rw [hexp, pow_add, pow_add, pow_one, sq]
      have hinv' : 2 ^ (2 * p - 1) * (y - n.sqrt - 1) ≤ n.sqrt := by
        apply Nat.le_of_mul_le_mul_left _ hsqrt_pos
        calc
          n.sqrt * (2 ^ (2 * p - 1) * (y - n.sqrt - 1))
              = (2 ^ (p - 1)) ^ 2 * (2 * n.sqrt * (y - n.sqrt - 1)) := by
                rw [hpow_eq]; ring
          _ ≤ (2 ^ (p - 1)) ^ 2 * (x - n.sqrt - 1) ^ 2 :=
                Nat.mul_le_mul_left _ hquad
          _ = (2 ^ (p - 1) * (x - n.sqrt - 1)) ^ 2 := by ring
          _ ≤ n.sqrt ^ 2 := Nat.pow_le_pow_left hinv 2
          _ = n.sqrt * n.sqrt := by ring
      have hk' : n.sqrt < 2 ^ (2 ^ k * (2 * p) - 1) := by
        have : 2 ^ k * (2 * p) = 2 ^ (k + 1) * p := by ring
        rwa [this]
      have hih := newtonLoop_time_le_of_pow_mul_le n hn k y (2 * p) hy_ge
        (by omega) hinv' hk'
      omega
    · omega

/--
Explicit doubly logarithmic tick bound:
\[
\operatorname{time}(\operatorname{seededSqrt}(n))
  \leq\left\lfloor\log_2\bigl(\lfloor\log_2 n\rfloor+2\bigr)\right\rfloor+3 .
\]
The seed corresponds to $p=1$, and $s<2^{2^k-1}$ for
$k=\lfloor\log_2(\lfloor\log_2 n\rfloor+2)\rfloor+1$; the doubling induction
then gives the claim.
-/
theorem seededSqrt_time_le (n : ℕ) :
    (seededSqrt n).time ≤ Nat.log 2 (Nat.log 2 n + 2) + 3 := by
  unfold seededSqrt
  split_ifs with h0
  · simp
  · have hn : 0 < n := Nat.pos_of_ne_zero h0
    set k := Nat.log 2 (Nat.log 2 n + 2) + 1
    have hinv : 2 ^ (1 - 1) * (newtonSeed n - n.sqrt - 1) ≤ n.sqrt := by
      have hseed := newtonSeed_le_two_mul_sqrt n hn
      simp only [Nat.sub_self, pow_zero, one_mul]
      omega
    have hk_pow : Nat.log 2 n + 2 < 2 ^ k :=
      Nat.lt_pow_succ_log_self (by norm_num) (Nat.log 2 n + 2)
    have hk : n.sqrt < 2 ^ (2 ^ k * 1 - 1) := by
      have h1 : n.sqrt ≤ n := Nat.sqrt_le_self n
      have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      have h3 : 2 ^ (Nat.log 2 n + 1) ≤ 2 ^ (2 ^ k * 1 - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)
    have hbound :=
      newtonLoop_time_le_of_pow_mul_le n hn k (newtonSeed n) 1
        (sqrt_le_newtonSeed n) le_rfl hinv hk
    omega

end NewtonRaphsonCC
