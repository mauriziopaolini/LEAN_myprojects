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

/- try to use Finset(s) for the "main" theorem (work in progress)-/

theorem main (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : Finset.card nodes = n + 1)
    (h_nodes_in_ab : ∀ x ∈ nodes, x ∈ (Icc a b))
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ nodes, f (x) = 0)
    : ∃ c ∈ Ioo a b, iteratedDeriv n f c = 0 := by

  have h_ordered_nodes_extra : ∃ x' : ℕ → ℝ, a ≤ x' 0 ∧ x' n ≤ b ∧
      (∀ k < n, (x' k) < x' (k+1)) ∧
      (∀ k ≤ n, f (x' k) = 0) := by
    sorry

  obtain ⟨x', hx'⟩ := h_ordered_nodes_extra

  have hx0 : a ≤ x' 0 := by exact hx'.1
  have hxn : x' n ≤ b := by exact hx'.2.1
  have h_ordered_nodes : ∀ k < n, (x' k) < x' (k+1) := by
    exact hx'.2.2.1
  have zerof' : ∀ k ≤ n, f (x' k) = 0 := by
    exact hx'.2.2.2

-- FIX!!!
  have hc : ∃ c ∈ Ioo (x' 0) (x' n) : iteratedDeriv n f c = 0 := by
    apply extRolle n hn_ne_0 hab hx0 hxn h_ordered_nodes hfc hf zerof'

/-
  example of using the theorem
-/

noncomputable def mynodes : Finset ℝ := {0, 2, 1}

theorem main0 (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hx0 : a ≤ x 0) (hxn : x n ≤ b)
    (h_ordered_nodes: ∀ k < n, (x k) < x (k+1))
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ k ≤ n, f (x k) = 0)
    : ∃ c ∈ Ioo (x 0) (x n), iteratedDeriv n f c = 0 := by

  apply extRolle n hn_ne_0 hab hx0 hxn h_ordered_nodes hfc hf zerof
