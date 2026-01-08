/-
This project proves an extended version of Rolle's theorem, namely if we have n+1 ordered nodes in
interval [a,b] where the C^n function f vanishes, then there exists a point c within the nodes
where the n-th derivative of f vanishes
-/

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import DividedDifference.Defs
import DividedDifference.Lemmas

open Set

variable {f : ℝ → ℝ} {a b : ℝ} {x : ℕ → ℝ} {n p q : ℕ}

theorem extRolle (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
  (hx0 : a ≤ x 0) (hxn : x n ≤ b)
  (h_ordered_nodes: ∀ k < n, (x k) < x (k+1))
  (hfc : ContinuousOn f (Icc a b))
  (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
  (zerof : ∀ k ≤ n, f (x k) = 0)
  : ∃ c ∈ Ioo a b, iteratedDeriv n f c = 0 := by

    cases h:n
    case zero =>
      rw [h] at hn_ne_0
      exfalso
      tauto
    case succ m =>
      rw [h] at hn_ne_0
      rw [h] at hxn
      rw [h] at h_ordered_nodes
      rw [h] at zerof
      rw [h] at hf
      clear h n
      induction hm:m generalizing f x m a b

      case zero =>
        let ⟨y, hy_prop⟩ := multiRolle hn_ne_0 hab hx0 hxn h_ordered_nodes hfc zerof
        rw [hm] at hxn
        rw [hm] at hy_prop
        rw [zero_add] at hy_prop
        rw [zero_add] at hxn
        rw [zero_add]
        rw [iteratedDeriv_one]
        use y 0
        have hy0_prop : (deriv f) (y 0) = 0 ∧ (y 0 > x 0) ∧ (y 0 < x 1) := by
          specialize hy_prop 0 (by linarith)
          exact hy_prop
        have hy0_gtx0 : y 0 > x 0 := by
          exact hy0_prop.right.left
        have hy0_ltx1 : y 0 < x 1 := by
          exact hy0_prop.right.right
        have hy0_ga : y 0 > a := by
          apply lt_of_le_of_lt at hx0
          exact hx0 hy0_gtx0
        have hy0_lb : y 0 < b := by
          apply lt_of_lt_of_le at hy0_ltx1
          exact hy0_ltx1 hxn
        have hy0_memab : y 0 ∈ Ioo a b := by
          exact ⟨hy0_ga, hy0_lb⟩
        use hy0_memab
        exact hy0_prop.left

      case succ mm ih =>
        let ⟨y, hy_prop⟩ := multiRolle hn_ne_0 hab hx0 hxn h_ordered_nodes hfc zerof
        -- rw [hm] at h
        rw [hm] at hxn
        rw [hm] at h_ordered_nodes
        rw [hm] at zerof
        rw [hm] at hf
        rw [hm] at hy_prop
        rw [hm] at hn_ne_0
        clear hm
        let fp := deriv f
        let fp_ab := derivWithin f (Ioo a b)
        simp at ih
        rw [iteratedDeriv_succ']

        have ffp0 : ContinuousOn (deriv f) (Ioo a b) := by
          apply regularderiv0 f a b mm
          norm_cast

        have ffp : ContDiffOn ℝ (mm) (deriv f) (Ioo a b) := by
          apply regularderiv f a b mm
          norm_cast

        have hy0 : y 0 ≤ y 0 := by
          simp
        have y0ltymm1 : y 0 < y (mm + 1) := by
          clear ih
          clear hf
          clear ffp
          induction hmm:mm generalizing mm
          case zero =>
            simp
            grind
          case succ mmm hmmm =>
            have hmmmy : y (mmm + 1) < y (mmm + 1 + 1) := by
              grind
            specialize hmmm mmm
            grind

        have hay0 : a < y 0 := by
          grind
        have hymmp1b : y (mm + 1) < b := by
          grind
        have hay0' : a ≤ y 0 := by
          grind
        have hymmp1b' : y (mm + 1) ≤ b := by
          grind

        have yy_in_ab : (Icc (y 0) (y (mm+1))) ⊆ (Ioo a b) := by
          apply Icc_subset_Ioo hay0 hymmp1b

        have yy_in_ab_oo : (Ioo (y 0) (y (mm+1))) ⊆ (Ioo a b) := by
          apply Ioo_subset_Ioo hay0' hymmp1b'

        have hfpc : ContinuousOn fp (Icc (y 0) (y (mm+1))) := by
          apply ContinuousOn.mono ffp0 yy_in_ab

        have ffp' : ContDiffOn ℝ (mm) fp (Ioo (y 0) (y (mm+1))) := by
          apply ContDiffOn.mono ffp yy_in_ab_oo

        have zerofp : ∀ k ≤ mm + 1, fp (y k) = 0 := by
          grind
        have h_ordered_nodesy : ∀ k < mm+1, y k < y (k + 1) := by
          grind
        specialize ih y0ltymm1 hy0 hfpc mm ffp' zerofp h_ordered_nodesy
        simp at ih
        grind

/-!
excerpt from Rolle.lean
----------------------------
# Rolle's Theorem

In this file we prove Rolle's Theorem. The theorem says that for a function `f : ℝ → ℝ` such that

* $f$ is differentiable on an open interval $(a, b)$, $a < b$;
* $f$ is continuous on the corresponding closed interval $[a, b]$;
* $f(a) = f(b)$,

there exists a point $c∈(a, b)$ such that $f'(c)=0$.

We prove four versions of this theorem.

* `exists_hasDerivAt_eq_zero` is closest to the statement given above. It assumes that at every
  point $x ∈ (a, b)$ function $f$ has derivative $f'(x)$, then concludes that $f'(c)=0$ for some
  $c∈(a, b)$.
* `exists_deriv_eq_zero` deals with `deriv f` instead of an arbitrary function `f'` and a predicate
  `HasDerivAt`; since we use zero as the "junk" value for `deriv f c`, this version does not
  assume that `f` is differentiable on the open interval.
* `exists_hasDerivAt_eq_zero'` is similar to `exists_hasDerivAt_eq_zero` but instead of assuming
  continuity on the closed interval $[a, b]$ it assumes that $f$ tends to the same limit as $x$
  tends to $a$ from the right and as $x$ tends to $b$ from the left.
* `exists_deriv_eq_zero'` relates to `exists_deriv_eq_zero` as `exists_hasDerivAt_eq_zero'`
  relates to `exists_hasDerivAt_eq_zero`.

## References

* [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem);

## Tags

local extremum, Rolle's Theorem
-/

@[expose] public section

open Set Filter Topology

variable {f f' : ℝ → ℝ} {a b l : ℝ}

/-- **Rolle's Theorem** `HasDerivAt` version -/
theorem my_exists_hasDerivAt_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) : ∃ c ∈ Ioo a b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  ⟨c, cmem, hc.hasDerivAt_eq_zero <| hff' c cmem⟩

/-- **Rolle's Theorem** `deriv` version -/
theorem my_exists_deriv_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  ⟨c, cmem, hc.deriv_eq_zero⟩


example (x : ℝ) : x - x = 0 := by simp  -- The `simp` tactic simplifies the expression to `0`
