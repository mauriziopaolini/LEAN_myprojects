-- This module serves as the root of the `DividedDifference` library.
-- Import modules here that should be built as part of the library.

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Lagrange
import DividedDifference.HigherOrderRolle
import DividedDifference.Polynomials
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

import Batteries.Tactic.GeneralizeProofs

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

- order_n_Rolle_F

The nodes are indicated as a Finset ℝ, hence they are unordered.  The resulting c is
shown to belong to the interior of the Convex hull of the set of nodes.

- order_n_Rolle_F_weak

same as above, but the resulting c is only shown to belong to the open interval (a,b).
This could be useful if one does not want to use the definition of
"intOfHull" (the interior of the convex hull of the set of nodes) which might be
inconvenient to manage.  Still of course the user can take a and b as the minimum
and maximum of the nodes and still recovere the stronger result

- order_n_Rolle_unorderedL (obsoleted)

same as above, but the nodes are not required to be in increasing order.  Of course
they must be mutually disjoint

- order_n_Rolle_unorderedL_weak (obsoleted)

weaker version of above, where the resulting point c is only guaranteed to
be in (a,b).
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

open Set Fin Filter Function
open scoped NNReal Topology ContDiff

theorem divided_difference_eq_deriv_n (n : ℕ) (hn_ne_0 : n ≠ 0) (nodes : Finset ℝ)
    (hab : a < b)
    (hcard : nodes.card = n + 1)
    (nodesinab : ∀ x ∈ nodes, x ∈ Icc a b)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ n f (Ioo a b))
    : ∃ c ∈ intOfHull nodes, divided_difference f nodes = (iteratedDeriv n f c)/(Nat.factorial n) := by

  let p := Lagrange.interpolate nodes my_id f
  let E := f - p.eval

  have hvs : Set.InjOn my_id nodes := by
    exact Function.Injective.injOn fun ⦃a₁ a₂⦄ a => a

  have zeroE : ∀ x ∈ nodes, E x = 0 := by
    have hinterp : ∀ x ∈ nodes, p.eval x = f x := by
      --have hvs : Set.InjOn my_id nodes := by
      --  exact Function.Injective.injOn fun ⦃a₁ a₂⦄ a => a

      intro x hx
      apply Lagrange.eval_interpolate_at_node f hvs hx

    aesop

  have hpc : ContinuousOn p.eval (Icc a b) := by
    exact Polynomial.continuousOn_aeval p

  have hpmc : ContinuousOn (- p.eval) (Icc a b) := by
    simp_all only [ne_eq, mem_Icc, continuousOn_neg_iff]

  have hEc : ContinuousOn (f - p.eval) (Icc a b) := by
    apply ContinuousOn.sub hfc hpc

  have hp : ContDiffOn ℝ n p.eval (Ioo a b) := by
    apply contdiffpol n p

  have hE : ContDiffOn ℝ n (f - p.eval) (Ioo a b) := by
    apply ContDiffOn.sub hf hp

  have nm1len : ↑n - 1 ≤ (n : WithTop ℕ∞):= by norm_num

  have hE' : ContDiffOn ℝ (n-1) (f - p.eval) (Ioo a b) := by
    apply ContDiffOn.of_le hE nm1len

  have exists_c : ∃ c ∈ intOfHull nodes, iteratedDeriv n E c = 0 := by
    apply order_n_Rolle_F n hn_ne_0 nodes hcard hab nodesinab hEc hE' zeroE

  obtain ⟨c, hc1, hc2⟩ := exists_c
  use c
  constructor
  exact hc1

  let p_deriv_n := iteratedDeriv n p.eval

  have nodes_nonempty : nodes.Nonempty := by
    have nodes_card_gt_0 : nodes.card > 0 := by
      grind
    exact Finset.card_pos.mp nodes_card_gt_0

  have c_in_ab : c ∈ (Ioo a b) := by
    unfold intOfHull at hc1
    constructor
    split_ifs at hc1
    have minisnode : (nodes.min' nodes_nonempty) ∈ nodes := by
      exact Finset.min'_mem nodes nodes_nonempty
    have min_lt_c : (nodes.min' nodes_nonempty) < c := by
      simp_all only [ne_eq, mem_Icc, continuousOn_neg_iff,
        tsub_le_iff_right, self_le_add_right, mem_Ioo]
    grind
    have c_lt_max : c < (nodes.max' nodes_nonempty) := by
      simp_all only [ne_eq, mem_Icc, continuousOn_neg_iff,
        tsub_le_iff_right, self_le_add_right, ↓reduceDIte, mem_Ioo]
    have maxisnode : (nodes.max' nodes_nonempty) ∈ nodes := by
      exact Finset.max'_mem nodes nodes_nonempty
    grind

  have contdiff_f : ContDiffAt ℝ n f c := by
    have isopen : IsOpen (Ioo a b) := by
      exact isOpen_Ioo

    have ioo_is_neigh : (Ioo a b) ∈ 𝓝 c := by
      exact IsOpen.mem_nhds isopen c_in_ab

    exact ContDiffOn.contDiffAt hf ioo_is_neigh

  have contdiff_p : ContDiffAt ℝ n p.eval c := by
    apply contdiffatpol

  have hderivs' : (iteratedDeriv n E c) = (iteratedDeriv n f c) - (p_deriv_n c) := by
    apply iteratedDeriv_sub contdiff_f contdiff_p

  have hderivs : (iteratedDeriv n f c) = (iteratedDeriv n E c) + (p_deriv_n c) := by
    grind

  have pol_as_function : (Polynomial.derivative^[n] p).eval c = p_deriv_n c:= by
    apply polynomial_derivatives_as_function

  have p_deriv_n_val : p_deriv_n c = (Nat.factorial n) * (divided_difference f nodes) := by
    unfold divided_difference
    have haddsum : n + 1 - 1 = n := by simp
    rw [hcard, haddsum]
    have p_deriv_n_is_coeff : p_deriv_n c = (Nat.factorial n)*(p.coeff n) := by

      have pdegree : p.degree ≤ (n : ℕ) := by
        have n_eq_card_m_1 : n = nodes.card - 1 := by
          grind
        rw [n_eq_card_m_1]
        exact Lagrange.degree_interpolate_le f hvs

      have p_deriv_n_is_coeff' : (Polynomial.derivative^[n] p).eval c = (Nat.factorial n)*(p.coeff n) := by
        exact derivnisfactorial pdegree

      rw [← pol_as_function]
      gcongr

    rw [p_deriv_n_is_coeff]

  field_simp
  rw [hderivs,hc2,zero_add,p_deriv_n_val]
  ring



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
