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

/-
def push_vec (a : ℝ) (x: ℕ → ℝ) : (ℕ → ℝ)
  | 0    => a
  | n+1  => x n

def pop_vec (x: ℕ → ℝ) : (ℕ → ℝ)
  | n    => x (n+1)

lemma pop_vec_v (k : ℕ) (x : ℕ → ℝ) (y : ℕ → ℝ) (h : y = pop_vec x) : y k = x (k+1) := by
  rw [h]
  rfl

lemma push_vec_v (k : ℕ) (x : ℕ → ℝ) (y : ℕ → ℝ) (a : ℝ) (h : y = push_vec a x) :
  y (k+1) = x k := by
    rw [h]
    rfl

lemma push_vec_v0 (x : ℕ → ℝ) (y : ℕ → ℝ) (a : ℝ) (h : y = push_vec a x) :
  y 0 = a := by
    rw [h]
    rfl
-/

/-
lemma strictMono_leq_n (n : ℕ) (x : ℕ → ℝ) (h_ordered_nodes: ∀ k < n, x k < x (k+1)) (hq : q ≤ n) (hp : p < q) :
  x p < x q := by

  cases hhq:q
  case zero =>
    rw [hhq] at hp
    tauto
  case succ qq =>
    rw [hhq] at hq
    rw [hhq] at hp
    clear hhq
    induction hhqq:qq generalizing qq
    case zero =>
      rw [hhqq] at hp
      rw [hhqq] at hq
      have hpzero : p = 0 := by
        linarith
      rw [hpzero]
      simp
      specialize h_ordered_nodes
      grind
    case succ qqq hqqq =>
      grind
-/

/-
lemma multiRolle (hn_ne_0 : n ≠ 0) (hab : a < b)
  (hx0 : a ≤ x 0) (hxn : x n ≤ b)
  (h_ordered_nodes: ∀ k < n, (x k) < x (k+1))
  (hfc : ContinuousOn f (Icc a b))
  (zerof : ∀ k ≤ n, f (x k) = 0)
  : ∃ (y : ℕ → ℝ) , ∀ k < n , ((deriv f) (y k) = 0 ∧ (y k > x k) ∧ (y k < x (k+1))) := by
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

      clear h
      induction hm:m generalizing m x a
      case zero =>
        rw [hm] at hxn
        rw [zero_add]
        have hx0x1 : x 0 < x 1 := h_ordered_nodes 0 (by linarith)
        have hfI : f (x 0) = f (x 1) := by
          rw [zerof 0 (by linarith)]
          rw [zerof 1 (by linarith)]
        have hfcx0x1 : ContinuousOn f (Icc (x 0) (x 1)) := by
          apply ContinuousOn.mono hfc
          apply Icc_subset_Icc
          exact hx0
          exact hxn

        let ⟨c, cmem, hc⟩ := exists_deriv_eq_zero hx0x1 hfcx0x1 hfI

        have cgtx0 : x 0 < c := by
          exact cmem.left
        have cltx1 : c < x 1 := by
          exact cmem.right
        have cgta : c > a := by
          apply lt_of_le_of_lt at hx0
          exact hx0 cgtx0
        have cltb : c < b := by
          apply lt_of_lt_of_le at cltx1
          exact cltx1 hxn
        have cmemab : c ∈ Ioo a b := by
          exact ⟨cgta, cltb⟩
        use fun k => if k = 0 then c else 0
        intro hk
        cases hk

        case succ kdum =>
          simp

        case zero =>
          simp
          use hc

      case succ mm ih =>
        have hx0x1 : x 0 < x 1 := by
          grind
        have hfI : f (x 0) = f (x 1) := by
          rw [zerof 0 (by linarith)]
          rw [zerof 1 (by linarith)]

        have hfcx0x1 : ContinuousOn f (Icc (x 0) (x 1)) := by
          apply ContinuousOn.mono hfc
          apply Icc_subset_Icc
          exact hx0
          have hx1ltxmp1 : x 1 < x (m+1) := by
            apply strictMono_leq_n (m + 1) x h_ordered_nodes
            simp
            simp
            rw [hm]
            simp

          rw [hm] at h_ordered_nodes
          clear ih
          grind

        let ⟨c, cmem, hc⟩ := exists_deriv_eq_zero hx0x1 hfcx0x1 hfI

        let x_cdr := pop_vec x

        rw [hm] at h_ordered_nodes
        rw [hm] at zerof

        have hcltb : c < b := by
          have cltx1 : c < x 1 := by
            grind

          have x1ltxmmp2 : x 1 < x (mm+2) := by
            apply strictMono_leq_n (mm + 2) x h_ordered_nodes
            simp
            grind

          have xmmp2leb : x (mm+2) ≤ b := by
            grind

          grind

        have halexcdr0 : c ≤ x_cdr 0 := by
          have x_cdr0eqx1 : x_cdr 0 = x 1 := by

            apply pop_vec_v 0 x x_cdr
            tauto

          grind

        have hfccb : ContinuousOn f (Icc c b) := by
          apply ContinuousOn.mono hfc
          apply Icc_subset_Icc
          grind
          simp

        have zerosf' : ∀ k ≤ mm + 1, f (x_cdr k) = 0 := by
          intro k hk
          have x_cdrkeqxkp1 : x_cdr k = x (k+1) := by

            apply pop_vec_v k x x_cdr
            tauto

          rw [x_cdrkeqxkp1]
          grind

        have h_ordered_nodes' : ∀ k < mm + 1, x_cdr k < x_cdr (k + 1) := by
          intro k
          have ht1 : x_cdr k = x (k+1) := by
            apply pop_vec_v k x x_cdr
            tauto
          have ht2 : x_cdr (k+1) = x (k+2) := by
            apply pop_vec_v (k+1) x x_cdr
            tauto
          rw [ht1]
          rw [ht2]
          grind

        have h_xcdrmmp1lexmmp2 : x_cdr (mm + 1) = x (mm + 2) := by
          apply pop_vec_v (mm + 1) x x_cdr
          tauto

        have h_xcdrmmp1leb : x_cdr (mm + 1) ≤ b := by
          grind

        have hn_ne_0' : mm + 1 ≠ 0 := by
          simp

        have hmm_eq_mm : mm = mm := by
          rfl

        specialize ih hcltb halexcdr0 hfccb mm zerosf' h_ordered_nodes' h_xcdrmmp1leb hn_ne_0' -- hmm_eq_mm

        specialize ih hmm_eq_mm

        obtain ⟨y_tail, hy_tail⟩ := ih

        let y := push_vec c y_tail
        use y
        intro k hk
        cases hk':k
        case zero =>
          have hfirst : y 0 = c := by
            apply push_vec_v0 y_tail y c
            rfl

          constructor
          rw [hfirst]
          exact hc

          rw [hfirst]
          grind

        case succ kk =>
          have hrest : y (kk + 1) = y_tail kk := by
            apply push_vec_v kk y_tail y c
            rfl

          rw [hrest]
          specialize hy_tail kk
          rw [hk'] at hk
          have hk'' : kk < mm + 1 := by
            grind

          constructor
          grind

          tauto
-/

/-
lemma regularderiv (f : ℝ → ℝ) (a b : ℝ) (mm : ℕ) (hf : ContDiffOn ℝ (mm + 1 + 1) f (Ioo a b)) :
    ContDiffOn ℝ (mm + 1) (deriv f) (Ioo a b) := by

  have hopen : IsOpen (Ioo a b) := by
    apply isOpen_Ioo

  apply ContDiffOn.deriv_of_isOpen hf hopen

  norm_cast

lemma f_eq_g_on_ab (f : ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ)
    (same : ∀ z ∈ (Ioo a b), f z = g z) (hcontf : ContinuousOn f (Ioo a b)) :
    ContinuousOn g (Ioo a b) := by

  have hopen : IsOpen (Ioo a b) := by
    apply isOpen_Ioo
  -- Since $f(z) = g(z)$ for all $z \in (a, b)$, and $f$ is continuous on $(a, b)$, it follows that $g$ is also continuous on $(a, b)$ by the fact that continuity is preserved under equality of functions.
  have h_cont_g : ContinuousOn (fun z => f z) (Set.Ioo a b) → ContinuousOn (fun z => g z) (Set.Ioo a b) := by
    -- Since $f(z) = g(z)$ for all $z \in (a, b)$, and $f$ is continuous on $(a, b)$, it follows that $g$ is also continuous on $(a, b)$ by the fact that equality of functions preserves continuity.
    intros hcontf_eq; exact (by
    -- Since $f$ and $g$ are equal on $(a, b)$, and $f$ is continuous on $(a, b)$, it follows that $g$ is also continuous on $(a, b)$ by the fact that equality of functions preserves continuity.
    apply ContinuousOn.congr hcontf_eq; exact fun z hz => same z hz ▸ rfl;);
  -- Apply the fact that if two functions are equal on an open set and one is continuous, then the other is also continuous.
  apply h_cont_g hcontf

lemma regularderiv0 (f : ℝ → ℝ) (a b : ℝ) (s : ℕ) (hf : ContDiffOn ℝ (s + 1 + 1) f (Ioo a b)) :
    ContinuousOn (deriv f) (Ioo a b) := by

  --let fp := deriv f
  --let fp2 := derivWithin f (Ioo a b)
  have ffp1 : ContinuousOn (iteratedDerivWithin 1 f (Ioo a b)) (Ioo a b) := by
    apply ContDiffOn.continuousOn_iteratedDerivWithin hf
    simp
    apply uniqueDiffOn_Ioo
  --have ffp : ContinuousOn (derivWithin f (Ioo a b)) (Ioo a b) := by
  have ffp : ContinuousOn (derivWithin f (Ioo a b)) (Ioo a b) := by
    rw [iteratedDerivWithin_one] at ffp1
    grind
  have hopen : IsOpen (Ioo a b) := by
    apply isOpen_Ioo
  --have same_in_ab : ∀ z ∈ (Ioo a b), (deriv f) z = (derivWithin f (Ioo a b)) z := by
  have same_in_ab : ∀ z ∈ (Ioo a b), (deriv f) z = (derivWithin f (Ioo a b)) z := by
    intro z hz
    rw [derivWithin_of_isOpen hopen]
    exact hz
  have same_in_ab' : ∀ z ∈ (Ioo a b), (derivWithin f (Ioo a b)) z = (deriv f) z := by
    intro z hz
    rw [derivWithin_of_isOpen hopen]
    exact hz
  apply f_eq_g_on_ab (derivWithin f (Ioo a b)) (deriv f)
  --exact hab
  exact same_in_ab'
  exact ffp
-/

theorem extRolle (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
  (hx0 : a ≤ x 0) (hxn : x n ≤ b)
  (h_ordered_nodes: ∀ k < n, (x k) < x (k+1))
  (hfc : ContinuousOn f (Icc a b))
  (hf : ContDiffOn ℝ n f (Ioo a b))
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

        have ffp : ContDiffOn ℝ (mm + 1) (deriv f) (Ioo a b) := by
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

        have ffp' : ContDiffOn ℝ (mm+1) fp (Ioo (y 0) (y (mm+1))) := by
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
