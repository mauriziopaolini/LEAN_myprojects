import Mathlib.Tactic

open Nat List

/-
 Let's try the James Oswald approach!
 With small adjustments to solve problems

https://jamesoswald.dev/posts/lean4-insertion-sort/
-/

--Inserts a number n into a sorted list such
--that the list remains sorted.
def sInsert (n : Nat) : List Nat -> List Nat
| [] => [n]
| h::t =>
  if n ≤ h then
    n :: h :: t
  else
    h :: sInsert n t

--The insertion sort algo
def mysort : List Nat -> List Nat
| [] => []
| h::t => sInsert h (mysort t)

--mysorted is a predicate that takes a list and returns iff it is sorted
def mysorted : List Nat -> Prop
--An empty list is sorted
| [] => True
--A list containing a single element is sorted
| [_] => True
--A list with 2 or more elements is only sorted if all
--elements are ordered.
| h1 :: h2 :: t => h1 ≤ h2 ∧ mysorted (h2 :: t)

/-
If a sorted list is passed to sInsert,
it will return a sorted list after inserting a new elm.
-/
lemma sInsert_sorted (l : List Nat) (n : Nat) :
mysorted l -> mysorted (sInsert n l) := by
  induction l
  --. case nil => simp [mysorted]
  . case nil =>
    finiteness
    --simp [mysorted]
  . case cons h1 t1 ih =>
    cases t1
    . case nil =>
      by_cases H2 : n ≤ h1
      . case pos => simp [sInsert, H2, mysorted]
      . case neg =>
        simp [sInsert, H2, mysorted]
        exact Nat.le_of_lt (Nat.lt_of_not_le H2)
    . case cons h2 t =>
      by_cases H2 : n ≤ h1
      . case pos => simp [sInsert, H2, mysorted]
      . case neg =>
        by_cases H3 : n ≤ h2
        . case pos =>
          simp [sInsert, H2, mysorted, H3]
          intro _
          apply And.intro
          . case left =>
            exact (Nat.le_of_lt (Nat.lt_of_not_le H2))
        . case neg =>
          simp [sInsert, H2, mysorted, H3]
          intros H4 H5
          apply And.intro
          . case left => exact H4
          . case right =>
            have ih2 := ih H5
            simp [sInsert, H3] at ih2
            exact ih2


theorem sort_sorted (l : List Nat) : mysorted (mysort l) := by
  induction l
  . case nil => simp [mysort, mysorted]
  . case cons h t ih =>
    simp [mysort]
    exact sInsert_sorted (mysort t) h ih


/-
A list l with n is a permutation of a list
the list with n inserted into it.
-/
lemma sInsert_perm (l : List Nat) (n : Nat) :
List.Perm (n::l) (sInsert n l) := by
  induction l
  . case nil => simp [sInsert]
  . case _ h t ih =>
    simp [sInsert]
    by_cases H : n ≤ h
    . case pos => simp [H]
    . case neg =>
      simp [H];
      apply (List.Perm.trans _ (List.Perm.cons h ih))
      exact List.Perm.swap h n t


/-
Sort returns a permutation of the input list.
-/
theorem sort_perm (l : List Nat) :
List.Perm l (mysort l) := by
  induction l
  . case nil => simp [mysort]
  . case cons h t ih =>
    simp [mysort]
    have H := sInsert_perm (mysort t) h
    have H2 := List.Perm.cons h ih
    exact List.Perm.trans H2 H
