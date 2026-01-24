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
  : ∃ c ∈ Ioo (x 0) (x n), iteratedDeriv n f c = 0 := by

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
        have hy0_memx0xn : y 0 ∈ Ioo (x 0) (x 1) := by
          exact ⟨hy0_gtx0, hy0_ltx1⟩
        use hy0_memx0xn
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

/-
Variant where the (n+1) nodes are given as a strictly increasing list
-/

theorem extRolle_L {listnodes : List ℝ} (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : listnodes.length = n + 1)
    (hx0 : a ≤ listnodes.getD 0 0) (hxn : listnodes.getD n 0 ≤ b)
    (h_ordered_nodes: ∀ k < n, (listnodes.getD k 0) < (listnodes.getD (k+1) 0))
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ listnodes, f x = 0)
    : ∃ c ∈ Ioo (listnodes.getD 0 0) (listnodes.getD n 0), iteratedDeriv n f c = 0 := by

  let xv := fun k => listnodes.getD k 0

  have hnonempty : listnodes.length > 0 := by
    grind
  have hgetD_in_list : ∀ k ≤ n, (listnodes.getD k 0) ∈ listnodes := by
    grind

  have hxvk_eq : ∀ k ≤ n, xv k = listnodes.getD k 0 := by
    grind
  have hxv0_eq : xv 0 = listnodes.getD 0 0 := by
    specialize hxvk_eq 0
    simp at hxvk_eq
    grind
  have hxvn_eq : listnodes.getD n 0 = xv n := by
    specialize hxvk_eq n
    simp at hxvk_eq
    grind
  have hx0' : a ≤ xv 0 := by
    grind

  have hxn' : xv n ≤ b := by
    grind

  have hxvk_eq : ∀ k ≤ n, xv k = listnodes.getD k 0 := by
    grind

  have hxvn_eq : listnodes.getD n 0 = xv n := by
    specialize hxvk_eq n
    simp at hxvk_eq
    grind

  have zerof' : ∀ k ≤ n, f (xv k) = 0 := by
    intro k hk
    specialize hxvk_eq k hk
    rw [hxvk_eq]
    specialize zerof (listnodes.getD k 0)
    specialize hgetD_in_list k hk
    specialize zerof hgetD_in_list
    exact zerof


  rw [← hxv0_eq]
  rw [hxvn_eq]
  apply extRolle n hn_ne_0 hab hx0' hxn' h_ordered_nodes hfc hf zerof'






variable {lnodes : List ℝ}

theorem extRolle_F (n : ℕ) (hn_ne_0 : n ≠ 0) (nodes : Finset ℝ)
    (hab : a < b)
    (hcard : nodes.card = n + 1)
    (hx0 : ∀ x ∈ nodes, a ≤ x) (hxn : ∀ x ∈ nodes, x ≤ b)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n - 1) f (Ioo a b))
    (zerof : ∀ x ∈ nodes, f x = 0)
    : ∃ c ∈ intOfHullS nodes, iteratedDeriv n f c = 0 := by
    --: ∃ c ∈ Ioo a b, iteratedDeriv n f c = 0 := by

  let lnodes : List ℝ := Finset.sort nodes

  have hsorted : List.Pairwise (. ≤ .) lnodes := by
    aesop

  have hnodup : lnodes.Nodup := by
    apply Finset.sort_nodup

  have hsorted' : ∀ i j : Fin lnodes.length, i < j → lnodes[i] < lnodes[j] := by
    intro i j hij
    have hw : lnodes[i] ≤ lnodes[j] := by
      apply List.pairwise_iff_get.1 hsorted _ _ hij
    have hne : lnodes[i] ≠ lnodes[j] := by
      unfold List.Nodup at hnodup
      apply List.pairwise_iff_get.1 hnodup _ _ hij

    grind

  have hcard' : lnodes.length = n+1 := by
    aesop

  have h_ordered_nodes : ∀ k < n, (lnodes.getD k 0) < (lnodes.getD (k+1) 0) := by
    intro i hi
    let j := i + 1

    have i_ln_np1 : i < n + 1 := by
      grind

    simp_all only [ne_eq, Fin.getElem_fin, List.getD_eq_getElem?_getD, add_lt_add_iff_right, getElem?_pos,
      Option.getD_some, gt_iff_lt]

    specialize hsorted'
    have rev_cast_i : ∃ ii : Fin lnodes.length, ii = i := by
      have hi' : i < lnodes.length := by
        rw [hcard']
        grind
      exact CanLift.prf i hi'

    obtain ⟨ii, hii⟩ := rev_cast_i

    have rev_cast_j : ∃ jj : Fin lnodes.length, jj = i+1 := by
      have hj' : j < lnodes.length := by
        rw [hcard']
        grind
      exact CanLift.prf j hj'

    obtain ⟨jj, hjj⟩ := rev_cast_j
    specialize hsorted' ii jj

    have ii_lt_jj : ii < jj := by
      grind

    specialize hsorted' ii_lt_jj
    grind

  have hx0' : ∀ x ∈ lnodes, a ≤ x := by aesop
  have hx0'' : a ≤ lnodes.getD 0 0 := by grind
  have hxn' : ∀ x ∈ lnodes, x ≤ b := by aesop
  have hxn'' : lnodes.getD n 0 ≤ b := by grind

  have zerof' : ∀ x ∈ lnodes, f x = 0 := by aesop

  have h_smaller : ∃ c ∈ Ioo (lnodes.getD 0 0) (lnodes.getD n 0), iteratedDeriv n f c = 0 := by

    apply extRolle_L n hn_ne_0 hab hcard' hx0'' hxn'' h_ordered_nodes hfc hf zerof'

  have hsame : Ioo (lnodes.getD 0 0) (lnodes.getD n 0) ⊆ intOfHullS nodes := by
    have nonempty0 : 0 < nodes.card := by grind

    have nonempty : nodes.Nonempty := by
      exact Finset.card_pos.mp nonempty0

    let nmin := nodes.min' nonempty
    let nmax := nodes.max' nonempty

    clear hfc hf zerof zerof'

    unfold intOfHullS

    split_ifs

    have hgen1 : ∀ x ∈ nodes, nmin ≤ x := by
      exact fun x a => Finset.min'_le nodes x a
    have hgen2 : ∀ x ∈ nodes, x ≤ nmax := by
      exact fun x a => Finset.le_max' nodes x a

    have hgen' : ∀ x ∈ lnodes, x ∈ nodes := by aesop

    have hgen1'' : lnodes.getD 0 0 ∈ nodes := by
      specialize hgen' (lnodes.getD 0 0)
      simp_all only [ne_eq, Fin.getElem_fin, List.getD_eq_getElem?_getD, add_lt_add_iff_right, getElem?_pos,
        Option.getD_some, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, List.getElem_mem, lt_add_iff_pos_right,
        mem_Ioo, forall_const]

    have hgen1''' : nmin ≤ lnodes.getD 0 0 := by
      simp_all only [ne_eq, Fin.getElem_fin, List.getD_eq_getElem?_getD, add_lt_add_iff_right, getElem?_pos,
        Option.getD_some, implies_true, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, List.getElem_mem,
        lt_add_iff_pos_right, mem_Ioo]

    have hgen2''' : lnodes.getD n 0 ≤ nmax := by
      simp_all only [ne_eq, Fin.getElem_fin, List.getD_eq_getElem?_getD, add_lt_add_iff_right, getElem?_pos,
        Option.getD_some, implies_true, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, List.getElem_mem,
        lt_add_iff_pos_right, mem_Ioo]

    have hgen2'' : lnodes.getD n 0 ∈ nodes := by
      specialize hgen' (lnodes.getD n 0)
      simp_all only [ne_eq, Fin.getElem_fin, List.getD_eq_getElem?_getD, add_lt_add_iff_right, getElem?_pos,
        Option.getD_some, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, List.getElem_mem, lt_add_iff_pos_right,
        mem_Ioo, forall_const]

    gcongr

  obtain ⟨c, hc⟩ := h_smaller
  obtain ⟨hc1, hc2⟩ := hc

  have h_subset : c ∈ intOfHullS nodes := by
    --have hc1 : c ∈ Ioo (lonodes.getD 0 0) (lonodes.getD n 0) := by
    --  tauto

    specialize hsame hc1
    exact hsame
  use c


theorem extRolle_F_weak (n : ℕ) (hn_ne_0 : n ≠ 0) (nodes : Finset ℝ)
    (hab : a < b)
    (hcard : nodes.card = n + 1)
    (hx0 : ∀ x ∈ nodes, a ≤ x) (hxn : ∀ x ∈ nodes, x ≤ b)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n - 1) f (Ioo a b))
    (zerof : ∀ x ∈ nodes, f x = 0)
    : ∃ c ∈ Ioo a b, iteratedDeriv n f c = 0 := by

  have c_in_intOfHullS : ∃ c ∈ intOfHullS nodes, iteratedDeriv n f c = 0 := by

    apply extRolle_F n hn_ne_0 nodes hab hcard hx0 hxn hfc hf zerof

  have hweaker : intOfHullS nodes ⊆ Ioo a b:= by
    have nonempty0 : 0 < nodes.card := by grind

    have nonempty : nodes.Nonempty := by
      exact Finset.card_pos.mp nonempty0

    let nmin := nodes.min' nonempty
    let nmax := nodes.max' nonempty

    clear hfc hf zerof

    unfold intOfHullS
    split_ifs


    have hgen1 : ∀ x ∈ nodes, nmin ≤ x := by
      exact fun x a => Finset.min'_le nodes x a
    have hgen2 : ∀ x ∈ nodes, x ≤ nmax := by
      exact fun x a => Finset.le_max' nodes x a

    gcongr

    exact (Finset.le_min'_iff nodes nonempty).mpr hx0

    exact Finset.max'_le nodes nonempty b hxn


  tauto



theorem extRolle_unorderedL (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : lnodes.length = n + 1)
    (hx0 : ∀ x ∈ lnodes, a ≤ x) (hxn : ∀ x ∈ lnodes, x ≤ b)
    (h_distinct_nodes : ∀ j ≤ n, ∀ i < j, lnodes.getD i 0 ≠ lnodes.getD j 0)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ lnodes, f x = 0)
    : ∃ c ∈ intOfHull lnodes, iteratedDeriv n f c = 0 := by

  let lonodes := mysort lnodes

  have isperm : List.Perm lnodes (mysort lnodes) := by
    exact sort_perm lnodes

  have hsamecard : lnodes.length = lonodes.length := by
    exact List.Perm.length_eq isperm

  have hcard_o : lonodes.length = n + 1 := by
    simp_all only [ne_eq, List.getD_eq_getElem?_getD]

  have hperm : ∀ i ≤ n, ∃ j ≤ n, lonodes.getD i 0 = lnodes.getD j 0 := by
    intro i hi
    let x := lonodes.getD i 0
    have hh : x ∈ lonodes := by
      grind

    have x_in_nodes : x ∈ lnodes := by
      grind
    have hhh : ∃ j < lnodes.length, lnodes.getD j 0 = x := by
      apply elem_to_index lnodes x x_in_nodes

    obtain ⟨j, hj⟩ := hhh
    use j

    rw [hj.2]
    constructor
    grind

    grind

  have hx0 : a ≤ lonodes.getD 0 0 := by
    specialize hperm 0
    simp at hperm
    obtain ⟨j, hj⟩ := hperm

    grind

  have hxn : lonodes.getD n 0 ≤ b := by
    specialize hperm n
    simp at hperm
    obtain ⟨j, hj⟩ := hperm
    grind

  have zerof' : ∀ x ∈ lonodes, f x = 0 := by
    intro x hx
    have hh : x ∈ lnodes := by
      grind
    grind

  have h_ordered_nodes_weak: ∀ k < n, (lonodes.getD k 0) ≤  (lonodes.getD (k+1) 0) := by
    have issorted : mysorted lonodes := by
      exact sort_sorted lnodes

    have hn : n = lonodes.length - 1 := by grind
    rw [hn]
    apply check_pairwise lonodes issorted

  have h_nodes_interval : Ioo (lonodes.getD 0 0) (lonodes.getD n 0) ⊆ Ioo a b := by
    grind

  have hcard' : n + 1 = lnodes.length := by
    rw [hcard]

  /- now we must make assumption h_ordered_nodes stronger with < instead of ≤ -/
  have h_distinct_nodes' : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → lnodes.getD i 0 ≠ lnodes.getD j 0 := by
    grind

  have h_distinct_nodes'' : ∀ ii < n+1, ∀ jj < n+1, ii ≠ jj → lonodes.getD ii 0 ≠ lonodes.getD jj 0 := by

    apply distinct_map_to_distinct lnodes lonodes hcard' isperm
    grind

  have h_ordered_nodes : ∀ k < n, (lonodes.getD k 0) < (lonodes.getD (k+1) 0) := by
    intro k hk
    specialize h_ordered_nodes_weak k hk
    have hk' : k < n + 1 := by grind
    have hk'' : k + 1 < n + 1 := by grind
    specialize h_distinct_nodes'' k hk' (k+1) hk''
    simp at h_distinct_nodes''
    push_neg at h_distinct_nodes''
    grind

  have h_smaller : ∃ c ∈ Ioo (lonodes.getD 0 0) (lonodes.getD n 0), iteratedDeriv n f c = 0 := by
    apply extRolle_L n hn_ne_0 hab hcard_o hx0 hxn h_ordered_nodes hfc hf zerof'

  have hsame : Ioo (lonodes.getD 0 0) (lonodes.getD n 0) ⊆ intOfHull lnodes := by
    have nonempty : 0 < lnodes.length := by grind

    let nmin := lnodes.minimum_of_length_pos nonempty
    let nmax := lnodes.maximum_of_length_pos nonempty

    --List.minimum_of_length_pos
    clear hfc hf zerof zerof'

    unfold intOfHull

    split_ifs

    have hgen : ∀ i ≤ n, nmin ≤ lnodes.getD i 0 ∧ lnodes.getD i 0 ≤ nmax := by
      intro i hi
      have i_lt_nlength : i < lnodes.length := by grind
      have x_in_lnodes : lnodes.getD i 0 ∈ lnodes := by grind

      constructor

      apply List.minimum_of_length_pos_le_of_mem x_in_lnodes nonempty

      apply List.le_maximum_of_length_pos_of_mem x_in_lnodes nonempty

    have hgen' : ∀ x ∈ lnodes, nmin ≤ x ∧ x ≤ nmax := by
      intro x hx

      have h_index : ∃ i < lnodes.length, lnodes.getD i 0 = x := by
        apply elem_to_index lnodes x
        exact hx
      obtain ⟨i, hi⟩ := h_index
      have i_le_n : i ≤ n := by grind
      specialize hgen i i_le_n
      have lnodes_i_eq_x : lnodes.getD i 0 = x := by grind
      rw [lnodes_i_eq_x] at hgen
      exact hgen

    grind
  obtain ⟨c, hc⟩ := h_smaller
  obtain ⟨hc1, hc2⟩ := hc

  have h_subset : c ∈ intOfHull lnodes := by
    --have hc1 : c ∈ Ioo (lonodes.getD 0 0) (lonodes.getD n 0) := by
    --  tauto

    specialize hsame hc1
    exact hsame
  use c


theorem extRolle_unorderedL_weak (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : lnodes.length = n + 1)
    (hx0 : ∀ x ∈ lnodes, a ≤ x) (hxn : ∀ x ∈ lnodes, x ≤ b)
    (h_distinct_nodes : ∀ j ≤ n, ∀ i < j, lnodes.getD i 0 ≠ lnodes.getD j 0)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ lnodes, f x = 0)
    : ∃ c ∈ Ioo a b, iteratedDeriv n f c = 0 := by

  have c_in_intOfHull : ∃ c ∈ intOfHull lnodes, iteratedDeriv n f c = 0 := by

    apply extRolle_unorderedL n hn_ne_0 hab hcard hx0 hxn h_distinct_nodes
        hfc hf zerof

  have hweaker : intOfHull lnodes ⊆ Ioo a b:= by
    have nonempty : 0 < lnodes.length := by grind

    let nmin := lnodes.minimum_of_length_pos nonempty
    let nmax := lnodes.maximum_of_length_pos nonempty

    clear hfc hf zerof

    unfold intOfHull
    split_ifs
    have nmin_in_lnodes : nmin ∈ lnodes := by
      exact List.minimum_of_length_pos_mem nonempty

    have nmax_in_lnodes : nmax ∈ lnodes := by
      exact List.maximum_of_length_pos_mem nonempty

    grind

  obtain ⟨c, hc⟩ := c_in_intOfHull
  obtain ⟨hc1, hc2⟩ := hc

  use c

  constructor
  tauto
  exact hc2
