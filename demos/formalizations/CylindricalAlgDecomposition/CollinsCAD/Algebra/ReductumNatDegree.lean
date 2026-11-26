import Mathlib
import Algebra.Reductum

namespace CollinsCAD

open Polynomial

/-- A nonzero reductum strictly decreases the natural degree:
    if $\operatorname{red}_{k+1}(p)\neq 0$, then
    $\deg(\operatorname{red}_{k+1}(p))<\deg(\operatorname{red}_k(p))$. -/
theorem reductum_natDegree_lt {R : Type*} [Semiring R] (p : Polynomial R) (k : ℕ)
    (h1 : reductum (k + 1) p ≠ 0) :
    (reductum (k + 1) p).natDegree < (reductum k p).natDegree := by
  rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero (reductum k p) with hlt | heq
  · simpa [reductum] using hlt
  · exact (h1 (by simpa [reductum] using heq)).elim

/-- Each reductum step removes at least one monomial from the support:
    $|\operatorname{supp}(\operatorname{red}_k(p))|\leq|\operatorname{supp}(p)|-k$. -/
theorem reductum_support_card_le {R : Type*} [Semiring R] (p : Polynomial R) (k : ℕ) :
    (reductum k p).support.card ≤ p.support.card - k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hcard := Polynomial.card_support_eraseLead (f := reductum k p)
      simp [reductum, hcard]
      omega

/-- After $|\operatorname{supp}(p)|$ reductum steps the polynomial vanishes:
    if $k\geq|\operatorname{supp}(p)|$, then $\operatorname{red}_k(p)=0$. -/
theorem reductum_eq_zero_of_support_card_le {R : Type*} [Semiring R]
    (p : Polynomial R) {k : ℕ} (hk : p.support.card ≤ k) :
    reductum k p = 0 := by
  have hcard := reductum_support_card_le p k
  have hzero : (reductum k p).support.card = 0 := by omega
  exact Polynomial.support_eq_empty.mp (Finset.card_eq_zero.mp hzero)

end CollinsCAD
