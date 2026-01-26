-- This module serves as the root of the `DividedDifference` library.
-- Import modules here that should be built as part of the library.

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Lagrange
import DividedDifference.HigherOrderRolle

open Set

variable {f : ℝ → ℝ} {a b : ℝ}

/-
There are four versions of the "order_n_Rolle".  It generally state that
a sufficiently regular function that vanishes at n+1 distinct nodes in [a,b]
admits a point within the set of nodes where its n-th derivative vanishes.

- order_n_Rolle_V

espects the n+1 nodes as the first values of a sequence x : ℕ → ℝ in strictly
increasing order, then the resulting point c satisfies c ∈ ( x 0, x n )

- order_n_Rolle_L

same as above, but the nodes are given as the elements of a List ℝ, still they
are required to be given in increasing order

- order_n_Rolle_unorderedL

same as above, but the nodes are not required to be in increasing order.  Of course
they must be mutually disjoint

- order_n_Rolle_unorderedL_weak

weaker version of above, where the resulting point c is only guaranteed to
be in (a,b).  This could be useful if one does not want to use the definition of
"intOfHull" (the interior of the convex hull of the set of nodes) which might be
inconvenient to manage.  Still of course the user can take a and b as the minimum
and maximum of the nodes and still recovere the stronger result
-/

/-
  nodes organized in a vector x : ℕ → ℝ
-/

theorem order_n_Rolle_V {x : ℕ → ℝ} (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hx0 : a ≤ x 0) (hxn : x n ≤ b)
    (h_ordered_nodes: ∀ k < n, (x k) < x (k+1))
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ k ≤ n, f (x k) = 0)
    : ∃ c ∈ Ioo (x 0) (x n), iteratedDeriv n f c = 0 := by

  apply extRolle n hn_ne_0 hab hx0 hxn h_ordered_nodes hfc hf zerof

/-
  In this variant the nodes are still ordered, but organized in a List
  structure
-/

theorem order_n_Rolle_L {listnodes : List ℝ} (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : listnodes.length = n + 1)
    (hx0 : a ≤ listnodes.getD 0 0) (hxn : listnodes.getD n 0 ≤ b)
    (h_ordered_nodes: ∀ k < n, (listnodes.getD k 0) < (listnodes.getD (k+1) 0))
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ listnodes, f x = 0)
    : ∃ c ∈ Ioo (listnodes.getD 0 0) (listnodes.getD n 0), iteratedDeriv n f c = 0 := by

  apply extRolle_L n hn_ne_0 hab hcard hx0 hxn h_ordered_nodes hfc hf zerof


/-
Main result: there is c ∈ intOfHullS of the nodes, the nodes are given as a
list of n+1 distict points in [a,b]
-/

theorem order_n_Rolle_F (n : ℕ) (hn_ne_0 : n ≠ 0)
    (nodes : Finset ℝ)
    (hcard : nodes.card = n + 1)
    (hab : a < b)
    (nodesinab : ∀ x ∈ nodes, x ∈ Icc a b)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n - 1) f (Ioo a b))
    (zerof : ∀ x ∈ nodes, f x = 0)
    : ∃ c ∈ intOfHull nodes, iteratedDeriv n f c = 0 := by

  apply extRolle_F n hn_ne_0 nodes hcard hab nodesinab hfc hf zerof

/-
Weak version where we are satisfied with c ∈ (a,b)
we should prove this using the main theorem
-/

theorem order_n_Rolle_F_weak (n : ℕ) (hn_ne_0 : n ≠ 0) (nodes : Finset ℝ)
    (hcard : nodes.card = n + 1)
    (hab : a < b)
    (nodesinab : ∀ x ∈ nodes, x ∈ Icc a b)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n - 1) f (Ioo a b))
    (zerof : ∀ x ∈ nodes, f x = 0)
    : ∃ c ∈ Ioo a b, iteratedDeriv n f c = 0 := by

  apply extRolle_F_weak n hn_ne_0 nodes hcard hab nodesinab hfc hf zerof


/-
Main result: order n divided difference equals the nth derivative of f divided
by n!
-/

theorem divided_difference_eq_deriv_n (n : ℕ) (hn_ne_0 : n ≠ 0) (nodes : Finset ℝ)
    (hab : a < b)
    (hcard : nodes.card = n + 1)
    (hx0 : ∀ x ∈ nodes, a ≤ x) (hxn : ∀ x ∈ nodes, x ≤ b)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n - 1) f (Ioo a b))
    : ∃ c ∈ intOfHull nodes, divided_difference f nodes = (iteratedDeriv n f c)/(Nat.factorial n) := by

  sorry



/-
Obsoleted: Main result: there is c ∈ intOfHull of the nodes, the nodes are given as a
list of n+1 distict points in [a,b]
-/

variable {lnodes : List ℝ}

theorem order_n_Rolle_unorderedL (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : lnodes.length = n + 1)
    (hx0 : ∀ x ∈ lnodes, a ≤ x) (hxn : ∀ x ∈ lnodes, x ≤ b)
    (h_distinct_nodes : ∀ j ≤ n, ∀ i < j, lnodes.getD i 0 ≠ lnodes.getD j 0)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ lnodes, f x = 0)
    : ∃ c ∈ intOfHullL lnodes, iteratedDeriv n f c = 0 := by

  apply extRolle_unorderedL n hn_ne_0 hab hcard hx0 hxn h_distinct_nodes hfc hf zerof


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

  apply extRolle_unorderedL_weak n hn_ne_0 hab hcard hx0 hxn h_distinct_nodes hfc hf zerof


/- Lagrange interpolation: given a finset `s : Finset ι`, a nodal map `v : ι → F` injective on
`s` and a value function `r : ι → F`, `interpolate s v r` is the unique
polynomial of degree `< #s` that takes value `r i` on `v i` for all `i` in `s`. -/

/-
def interpolate (s : Finset ι) (v : ι → F) : (ι → F) →ₗ[F] F[X] where
  toFun r := ∑ i ∈ s, C (r i) * Lagrange.basis s v i
  map_add' f g := by
    simp_rw [← Finset.sum_add_distrib]
    have h : (fun x => C (f x) * Lagrange.basis s v x + C (g x) * Lagrange.basis s v x) =
    (fun x => C ((f + g) x) * Lagrange.basis s v x) := by
      simp_rw [← add_mul, ← C_add, Pi.add_apply]
    rw [h]
  map_smul' c f := by
    simp_rw [Finset.smul_sum, C_mul', smul_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
-/

open Polynomial
namespace Polynomial
open Function Fintype
open scoped Finset

/-
def divided_difference (f : ℝ → ℝ) (lnodes : List ℝ) : ℝ :=
  0

theorem divided_difference_eq_nth_deriv (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : lnodes.length = n + 1)
    (hx0 : ∀ x ∈ lnodes, a ≤ x) (hxn : ∀ x ∈ lnodes, x ≤ b)
    (h_distinct_nodes : ∀ j ≤ n, ∀ i < j, lnodes.getD i 0 ≠ lnodes.getD j 0)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    : ∃ c ∈ Ioo a b, (divided_difference f lnodes) = iteratedDeriv n f c := by

  have hs : s = Finset (n+1)
  have hinterp : Lagrange.interpolate
  sorry


-/
