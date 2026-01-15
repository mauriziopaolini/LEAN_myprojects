-- This module serves as the root of the `DividedDifference` library.
-- Import modules here that should be built as part of the library.

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import DividedDifference.HigherOrderRolle
import DividedDifference.Sorting

open Set

variable {f : ℝ → ℝ} {a b : ℝ} {x : ℕ → ℝ} {n p q : ℕ} {nodes : Finset ℝ}

/-
main0 is exactly the theorem extRolle in divided_difference.lean
ideally one should e.g. allow for the nodes to be in any order.
See below
-/

/-
  example of using extRolle theorem
-/

/-
  nodes organized in a vector x : ℕ → ℝ
-/
theorem order_n_Rolle_V (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hx0 : a ≤ x 0) (hxn : x n ≤ b)
    (h_ordered_nodes: ∀ k < n, (x k) < x (k+1))
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ k ≤ n, f (x k) = 0)
    : ∃ c ∈ Ioo (x 0) (x n), iteratedDeriv n f c = 0 := by

  apply extRolle n hn_ne_0 hab hx0 hxn h_ordered_nodes hfc hf zerof

variable {listnodes: List ℝ}

/-
  In this variant the nodes are still ordered, but organized in a List
  structure
-/

theorem order_n_Rolle_L (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
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


/-
Main result: there is c ∈ intOfHull of the nodes, the nodes are given as a
list of n+1 distict points in [a,b]
-/

theorem order_n_Rolle_unorderedL (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
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
    apply order_n_Rolle_L n hn_ne_0 hab hcard_o hx0 hxn h_ordered_nodes hfc hf zerof'

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

/-
Weak version where we are satisfied with c ∈ (a,b)
we should prove this using the main theorem
-/

theorem order_n_Rolle_unorderedL_weak (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : lnodes.length = n + 1)
    (hx0 : ∀ x ∈ lnodes, a ≤ x) (hxn : ∀ x ∈ lnodes, x ≤ b)
    (h_distinct_nodes : ∀ j ≤ n, ∀ i < j, lnodes.getD i 0 ≠ lnodes.getD j 0)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ lnodes, f x = 0)
    : ∃ c ∈ Ioo a b, iteratedDeriv n f c = 0 := by

  have c_in_intOfHull : ∃ c ∈ intOfHull lnodes, iteratedDeriv n f c = 0 := by

    apply order_n_Rolle_unorderedL n hn_ne_0 hab hcard hx0 hxn h_distinct_nodes
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
