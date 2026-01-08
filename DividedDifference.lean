-- This module serves as the root of the `DividedDifference` library.
-- Import modules here that should be built as part of the library.

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import DividedDifference.divided_difference

open Set

variable {f : ℝ → ℝ} {a b : ℝ} {x : ℕ → ℝ} {n p q : ℕ}

/-
This is exactly the theorem extRolle in divided_difference.lean
ideally one should e.g. allow for the nodes to be in any order
-/

theorem main (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hx0 : a ≤ x 0) (hxn : x n ≤ b)
    (h_ordered_nodes: ∀ k < n, (x k) < x (k+1))
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ k ≤ n, f (x k) = 0)
    : ∃ c ∈ Ioo a b, iteratedDeriv n f c = 0 := by

  apply extRolle n hn_ne_0 hab hx0 hxn h_ordered_nodes hfc hf zerof
