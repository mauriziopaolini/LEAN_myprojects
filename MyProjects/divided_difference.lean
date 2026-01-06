/-
This is a comment
-/

-- import Mathlib.Analysis.Calculus.LocalExtr.Basic
-- import Mathlib.Topology.Order.Rolle
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs

open Set Filter Topology

variable {f : ℝ → ℝ} {a b : ℝ} {x : ℕ → ℝ} {n p q : ℕ}

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

/-
If x_k < x_{k+1} for all k < n, then x is strictly monotone on {0, ..., n}.
-/
lemma strictMonoOn_of_ordered_nodes_obsoleted (h_ordered_nodes: ∀ k < n, x k < x (k+1)) :
  StrictMonoOn x (Set.Iic n) := by

    -- refine StrictMono.strictMonoOn ?_ (Iic n)

    sorry

-- lemma strictMono_leq_n (h_ordered_nodes: ∀ k ≤ n, x k < x (k+1)) : ∀ q < n, ∀ p < q, x p < x q := by
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

        -- have h_increasing : StrictMonoOn x (Set.Iic (m+1)) :=
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

          -- have hx1leb : x 1 ≤ b := by
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

#check ContinuousOn.mono
#check (Ioo a b) ⊆ (Icc a b)

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem continuous_derivative_of_c1 {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s) :
    ContinuousOn (fderiv ℝ f) s := by
  -- ContDiffOn.continuousOn_fderiv provides the proof directly for C^n functions where n ≥ 1
  -- exact hf.continuousOn_fderiv hs le_rfl
  sorry

lemma cont_on_subset_unused (f : ℝ → ℝ) (a b c d: ℝ) (hab : a < b) (hac : a < c) (hcd : c < d)
  (hdb : d < b) (hf : ContDiffOn ℝ 1 f (Ioo a b)) : ContinuousOn (deriv f) (Icc c d) := by

    have sbset : (Icc c d) ⊆ (Ioo a b) := by
      intro x hx
      have h1 : a < x := lt_of_lt_of_le hac hx.1
      have h2 : x < b := lt_of_le_of_lt hx.2 hdb
      exact ⟨h1, h2⟩

    have hfp : ContDiffOn ℝ 0 (deriv f) (Ioo a b) := by
      intro y hy
      -- from `ContDiffOn ℝ 1 f (Ioo a b)` we get `ContDiffWithinAt ℝ 1 f (Ioo a b) y`
      have hfy : ContDiffWithinAt ℝ 1 f (Ioo a b) y := hf y hy
      -- the successor characterization gives continuity of the derivative (order 0)
      -- have hder := contDiffWithinAt_succ_iff_hasFDerivWithinAt hfy
      -- have hder := (ContDiffWithinAt.succ_iff.1 hfy).2
      -- exact hder

    -- `ContDiffOn ... 0` gives continuity, then restrict to the closed interval
    -- have hcont : ContinuousOn (deriv f) (Ioo a b) := ContDiffOn.continuousOn_zero hfp
    -- exact ContinuousOn.mono hcont sbset
    -- have hfp : ContDiffOn ℝ 0 (deriv f) (Ioo a b) :=

      sorry

    apply ContDiffOn.continuousOn_zero at hfp
    -- apply continuousOn_iff_continuous_restrict

    sorry

lemma extRolle (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
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
        -- rw [hm] at h
        -- rw [zero_add] at h
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
        clear hm
        let fp := deriv f
        simp at ih
        rw [iteratedDeriv_succ']
        have ffp : ContDiffOn ℝ (mm + 1) fp (Ioo a b) := by
          intro y hy
          have hfy : ContDiffWithinAt ℝ (mm + 1 + 1) f (Ioo a b) y := by
            specialize hf y hy
            exact hf
          have hfy_succ : ContDiffWithinAt ℝ (mm + 1) fp (Ioo a b) y := by
          -- rw [← ContDiffOn_succ_iff_deriv]
          -- apply ContDiff.deriv at hf
            sorry
          exact hfy_succ
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
        have hfpc : ContinuousOn fp (Icc (y 0) (y (mm+1))) := by
          sorry
        have ffp' : ContDiffOn ℝ (mm+1) fp (Ioo (y 0) (y (mm+1))) := by
          sorry
        have zerofp : ∀ k ≤ mm + 1, fp (y k) = 0 := by
          grind
        have h_ordered_nodesy : ∀ k < mm+1, y k < y (k + 1) := by
          grind
        specialize ih y0ltymm1 hy0 hfpc mm ffp' zerofp h_ordered_nodesy
        simp at ih
        grind

/-!
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
