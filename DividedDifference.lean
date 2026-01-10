-- This module serves as the root of the `DividedDifference` library.
-- Import modules here that should be built as part of the library.

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import DividedDifference.divided_difference

open Set

variable {f : ℝ → ℝ} {a b : ℝ} {x : ℕ → ℝ} {n p q : ℕ} {nodes : Finset ℝ}

/-
main0 is exactly the theorem extRolle in divided_difference.lean
ideally one should e.g. allow for the nodes to be in any order
-/

/-
  example of using extRolle theorem
-/


theorem main0 (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hx0 : a ≤ x 0) (hxn : x n ≤ b)
    (h_ordered_nodes: ∀ k < n, (x k) < x (k+1))
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ k ≤ n, f (x k) = 0)
    : ∃ c ∈ Ioo (x 0) (x n), iteratedDeriv n f c = 0 := by

  apply extRolle n hn_ne_0 hab hx0 hxn h_ordered_nodes hfc hf zerof







/- try to use Finset(s) for the "main" theorem (work in progress)-/

theorem main (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : Finset.card nodes = n + 1)
    (h_nodes_in_ab : ∀ x ∈ nodes, x ∈ (Icc a b))
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ nodes, f (x) = 0)
    : ∃ c ∈ intOfHull nodes, iteratedDeriv n f c = 0 := by

  let x' := get_ordered_n_nodes nodes (n+1)

  have hexistfirst : ∃ x ∈ nodes, x = x' 0 := by
    let ⟨node, hnode⟩ := get_ordered_n_nodes_v1 nodes (n+1) 0


    let ⟨ node⟩ = get_ordered_n_nodes_v1 nodes (n+1) 0

    apply get_ordered_n_nodes_v1

  have h_ordered_nodes_extra : a ≤ x' 0 ∧ x' n ≤ b ∧
      (∀ i ≤ n, ∀ j < i, (x' j) < x' i) ∧
      (∀ k ≤ n, f (x' k) = 0) := by

    constructor
    have hexist : ∃ x ∈ nodes : x = x' 0 := by

    apply get_ordered_n_nodes_v1 nodes (n+1) 0

    sorry

    constructor
    sorry

    constructor
    sorry

    sorry

    --apply get_ordered_n_nodes_v1 nodes (n+1) 0
    apply get_ordered_n_nodes_v0 nodes (n+1)
    unfold get_ordered_n_nodes

    obtain ⟨x',hx'⟩ := get_ordered_n_nodes nodes (n+1)

    sorry

  obtain ⟨x', hx'⟩ := h_ordered_nodes_extra

  have hx0 : a ≤ x' 0 := by exact hx'.1
  have hxn : x' n ≤ b := by exact hx'.2.1
  have h_ordered_nodes : ∀ k < n, (x' k) < x' (k+1) := by
    exact hx'.2.2.1
  have zerof' : ∀ k ≤ n, f (x' k) = 0 := by
    exact hx'.2.2.2

  have hc : ∃ cc ∈ Ioo (x' 0) (x' n), iteratedDeriv n f cc = 0 := by
    apply extRolle n hn_ne_0 hab hx0 hxn h_ordered_nodes hfc hf zerof'

  obtain ⟨c, hc'⟩ := hc
  have hcinx0xn : c ∈ Ioo (x' 0) (x' n) := by
    exact hc'.1
  use c
  constructor
  apply Ioo_subset_Ioo hx0 hxn
  exact hcinx0xn
  exact hc'.2
  sorry


noncomputable def mynodes : Finset ℝ := {0, 2, 1}

noncomputable def mynodesvec : ℕ → ℝ := get_ordered_n_nodes mynodes 3

#check Finset.min' mynodes
#check mynodesvec
