-- This module serves as the root of the `DividedDifference` library.
-- Import modules here that should be built as part of the library.

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import DividedDifference.divided_difference
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

/-
Some lemmas useful for the sorting version
-/

lemma check_pairwise (ls : List ℝ) (ls_is : mysorted ls) :
    ∀ k < ls.length - 1, ls.getD k 0 ≤ ls.getD (k+1) 0 := by

  intro k
  unfold mysorted at ls_is
  -- By induction on $k$, we can show that for any $k < \text{length}(ls) - 1$, the $k$-th element is less than or equal to the $(k+1)$-th element.
  induction' k with k ih generalizing ls;
  · rcases ls with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> norm_num at * ; tauto;
  · rcases ls with ( _ | ⟨ head, _ | ⟨ h2, t ⟩ ⟩ ) <;> norm_num at *;
    -- Apply the induction hypothesis to the list h2 :: t.
    specialize ih (h2 :: t);
    -- Apply the induction hypothesis to the list h2 :: t, using the fact that h2 :: t is sorted.
    apply ih; exact (by
    cases t <;> aesop)


lemma distinct_map_to_distinct {n : ℕ} (l1 l2 : List ℝ) (hn : n = l1.length) (isperm : List.Perm l1 l2)
    (distinct_l1: ∀ i < n, ∀ j < n, i ≠ j → l1.getD i 0 ≠ l1.getD j 0)
    : ∀ ii < n, ∀ jj < n, ii ≠ jj → l2.getD ii 0 ≠ l2.getD jj 0 := by

  by_contra
  push_neg at this

  obtain ⟨ii, hii⟩ := this
  have hii1 : ii < n := by grind
  have hii2 : ∃ jj < n, ii ≠ jj ∧ l2.getD ii 0 = l2.getD jj 0 := by grind

  obtain ⟨jj, hjj⟩ := hii2
  have hjj1 : jj < n := by grind
  have hjj2 : ii ≠ jj ∧ l2.getD ii 0 = l2.getD jj 0 := by grind
  have ii_ne_jj : ii ≠ jj := by grind
  have hjj3 : l2.getD ii 0 = l2.getD jj 0 := by grind

  sorry


lemma elem_to_index (l : List ℝ) (x : ℝ) (x_in_l : x ∈ l):
    ∃ j < l.length, l.getD j 0 = x := by
  apply List.mem_iff_get.1 x_in_l |> fun ⟨j, hj⟩ => ⟨j, by aesop⟩

variable {lnodes : List ℝ}

theorem order_n_Rolle_unorderedL (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : lnodes.length = n + 1)
    (hx0 : ∀ x ∈ lnodes, a ≤ x) (hxn : ∀ x ∈ lnodes, x ≤ b)
    (h_distinct_nodes : ∀ j ≤ n, ∀ i < j, lnodes.getD i 0 ≠ lnodes.getD j 0)
    --(h_distinct_nodes : ∀ i ∈ Fin (n+1), ∀ j ∈ Fin (n+1), i < j → lnodes.getD i 0 ≠ lnodes.getD j 0)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ lnodes, f x = 0)
    --: ∃ c ∈ intOfHull lnodes, iteratedDeriv n f c = 0 := by
    : ∃ c ∈ Ioo a b, iteratedDeriv n f c = 0 := by

  let lonodes := mysort lnodes

  --let myperm := List.Perm lnodes (mysort lnodes)
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
  --have hcard_o : lonodes.length = n + 1 := by
  --  grind
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

  obtain ⟨c, hc⟩ := h_smaller
  use c

  tauto
