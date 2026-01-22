/-
We use a "vector" to store the nodes, we need to use it like a stack
-/

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Lagrange

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

open Set List

/-
noncomputable def myminimum' (lnodes : List ℕ) : ℕ :=

  if lnodes.length = 0 then
    0
  else
    lnodes.getD (List.argmin id lnodes) 0
    have hnonempty : 0 < lnodes.length := by

      sorry

    List.coe_minimum_of_length_pos
-/

def intOfHull (lnodes : List ℝ) : Set ℝ :=
  if nonempty : 0 < lnodes.length then
    -- lnodes is nonempty
    Ioo (List.minimum_of_length_pos nonempty) (List.maximum_of_length_pos nonempty)
  else
    ∅

def intOfHullS (nodes : Finset ℝ) : Set ℝ :=
  if nonempty : nodes.Nonempty then
    -- nodes is nonempty
    Ioo (Finset.min' nodes nonempty) (Finset.max' nodes nonempty)
  else
    ∅

/-
Definition of divided difference.  It takes three arguments:
- s: a Finset ℕ (set of indices)
- v: vector of nodes
- r: vector of nodal values of some function
-/

open Polynomial

noncomputable def divided_difference (s : Finset ℕ) (v : ℕ → ℝ) (r : ℕ → ℝ) : ℝ :=
  coeff (Lagrange.interpolate s v r) (s.card - 1)


lemma divided_difference_is_exact {n : ℕ} (s : Finset ℕ) (v : ℕ → ℝ) (r : ℕ → ℝ) (hcard : s.card = n+1):
    divided_difference s v r = coeff (Lagrange.interpolate s v r) n := by

  unfold divided_difference
  rw [hcard]
  simp
