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

  have hcard : lonodes.length = n + 1 := by
    sorry

  have hx0 : a ≤ lonodes.getD 0 0 := by
    sorry

  have hxn : lonodes.getD n 0 ≤ b := by
    sorry

  have zerof' : ∀ x ∈ lonodes, f x = 0 := by
    sorry

  have h_ordered_nodes: ∀ k < n, (lonodes.getD k 0) < (lonodes.getD (k+1) 0) := by
    sorry

  have h_nodes_interval : Ioo (lonodes.getD 0 0) (lonodes.getD n 0) ⊆ Ioo a b := by
    sorry

  have h_smaller : ∃ c ∈ Ioo (lonodes.getD 0 0) (lonodes.getD n 0), iteratedDeriv n f c = 0 := by
    apply order_n_Rolle_L n hn_ne_0 hab hcard hx0 hxn h_ordered_nodes hfc hf zerof'

  obtain ⟨c, hc⟩ := h_smaller
  use c

  tauto
