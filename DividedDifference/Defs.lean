/-
We use a "vector" to store the nodes, we need to use it like a stack
-/

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic

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

open Set

def intOfHull (nodes : Finset ℝ) : Set ℝ :=
  if nonempty : nodes.Nonempty then
    -- nodes is nonempty
    Ioo (Finset.min' nodes nonempty) (Finset.max' nodes nonempty)
  else
    ∅

noncomputable def remove_min_node (nodes : Finset ℝ) (H : nodes.Nonempty) : Finset ℝ :=
  Finset.erase nodes (Finset.min' nodes H)

/-
build a vector containing the smaller n elements of the set "nodes"
or all elements if n < card nodes
-/

noncomputable def get_ordered_n_nodes (nodes : Finset ℝ) (n : ℕ) : ℕ → ℝ :=
  if nonempty : nodes.Nonempty then
    -- nodes is nonempty
    if n_ne_0 : n > 0 then
      push_vec (Finset.min' nodes nonempty)
       (get_ordered_n_nodes (remove_min_node nodes nonempty) (n-1))
    else
      fun k => 0*k
  else
    fun k => 0*k

/- for now just comment this out -/

/-
lemma get_ordered_n_nodes_v0 (nodes : Finset ℝ) (n : ℕ) (x' : ℕ → ℝ)
    (h: x' = get_ordered_n_nodes nodes n) (n_eq_card : n = Finset.card nodes):
    ∀ i < n, ∀ j < i, x' j < x' i := by

  rw [h]
  unfold get_ordered_n_nodes
  intro i hi j hj

  cases hn : n
  case zero =>
    sorry
  case succ nn =>
    sorry

lemma get_ordered_n_nodes_v1 (nodes : Finset ℝ) (n : ℕ) (x' : ℕ → ℝ) (i : ℕ)
    (h : x' = get_ordered_n_nodes nodes n) (n_eq_card : n = Finset.card nodes) (hi : i < n):
    x' i ∈ nodes := by

  rw [h]
  unfold get_ordered_n_nodes

  cases hn : n
  case zero =>
    linarith
  case succ nn =>
    sorry
-/
