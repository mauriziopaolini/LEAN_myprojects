import Mathlib.Tactic

open Real Nat List

/-
This version is obsoleted, since Mathlib contains all the necessary
sorting tools

 Let's try the James Oswald approach!
 With small adjustments to solve problems

https://jamesoswald.dev/posts/lean4-insertion-sort/
-/

--Inserts a number n into a sorted list such
--that the list remains sorted.
noncomputable def sInsert (a : ℝ) : List ℝ → List ℝ
| [] => [a]
| h::t =>
  if a ≤ h then
    a :: h :: t
  else
    h :: sInsert a t

--The insertion sort algo
noncomputable def mysort : List ℝ -> List ℝ
| [] => []
| h::t => sInsert h (mysort t)

--mysorted is a predicate that takes a list and returns iff it is sorted
def mysorted : List ℝ -> Prop
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
lemma sInsert_sorted (l : List ℝ) (a : ℝ) :
mysorted l -> mysorted (sInsert a l) := by
  induction l
  --. case nil => simp [mysorted]
  . case nil =>
    finiteness
    --simp [mysorted]
  . case cons h1 t1 ih =>
    cases t1
    . case nil =>
      by_cases H2 : a ≤ h1
      . case pos => simp [sInsert, H2, mysorted]
      . case neg =>
        simp [sInsert, H2, mysorted]
        exact Std.le_of_not_ge H2
        --exact Real.le_of_lt (Real.lt_of_not_le H2)
    . case cons h2 t =>
      by_cases H2 : a ≤ h1
      . case pos => simp [sInsert, H2, mysorted]
      . case neg =>
        by_cases H3 : a ≤ h2
        . case pos =>
          simp [sInsert, H2, mysorted, H3]
          intro _
          apply And.intro
          . case left =>
            exact Std.le_of_not_ge H2
            --exact (Nat.le_of_lt (Nat.lt_of_not_le H2))
        . case neg =>
          simp [sInsert, H2, mysorted, H3]
          intros H4 H5
          apply And.intro
          . case left => exact H4
          . case right =>
            have ih2 := ih H5
            simp [sInsert, H3] at ih2
            exact ih2


theorem sort_sorted (l : List ℝ) : mysorted (mysort l) := by
  induction l
  . case nil => simp [mysort, mysorted]
  . case cons h t ih =>
    simp [mysort]
    exact sInsert_sorted (mysort t) h ih


/-
A list l with a is a permutation of a list
the list with a inserted into it.
-/
lemma sInsert_perm (l : List ℝ) (a : ℝ) :
List.Perm (a::l) (sInsert a l) := by
  induction l
  . case nil => simp [sInsert]
  . case _ h t ih =>
    simp [sInsert]
    by_cases H : a ≤ h
    . case pos => simp [H]
    . case neg =>
      simp [H];
      apply (List.Perm.trans _ (List.Perm.cons h ih))
      exact List.Perm.swap h a t


/-
Sort returns a permutation of the input list.
-/
theorem sort_perm (l : List ℝ) :
List.Perm l (mysort l) := by
  induction l
  . case nil => simp [mysort]
  . case cons h t ih =>
    simp [mysort]
    have H := sInsert_perm (mysort t) h
    have H2 := List.Perm.cons h ih
    exact List.Perm.trans H2 H
