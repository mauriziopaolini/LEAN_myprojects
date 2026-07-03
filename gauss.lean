/-
 -/

import Mathlib

variable (x : ℝ) (i : ℕ)

theorem gaussind (n : ℕ) : (∑ i < n, i) = n*(n-1)/2 := by

  by_cases hnzero : n = 0
  rw [hnzero]
  have hempty : Finset.Iio 0 = ∅ := by
    norm_num

  have hsumempty : ∑ i ∈ ∅, i = 0 := by
    norm_num

  rw [hempty, hsumempty]

  set m := n - 1

  have hn : n = m + 1 := by grind

  rw [hn]
  -- clear hn
  clear hnzero

  induction hm:m generalizing m

  case neg.zero =>

    simp_all

  case neg.succ h1 h2 =>
    rw [hn] at h2
    simp_all
    sorry




theorem gaussrec (n : ℕ) : (∑ i < n, i) = n*(n-1)/2 := by

  by_cases hnzero : n = 0
  rw [hnzero]
  have hempty : Finset.Iio 0 = ∅ := by
    norm_num

  have hsumempty : ∑ i ∈ ∅, i = 0 := by
    norm_num

  rw [hempty, hsumempty]

  by_cases hnisone : n = 1
  have hf : Finset.Iio n = {0} := by
    grind

  rw [hf, hnisone]
  have hs : ∑ i ∈ {0}, i = 0 := by
    norm_num

  have hc : 1*(1-1)/2 = 0 := by
    gcongr

  rw [hc]
  exact hs

  set nm1 := n - 1
  have hnm1pos : nm1 > 0 := by
    omega

  have hprev : (∑ i < nm1, i) = nm1*(nm1-1)/2 := by
    apply gaussrec nm1

  have hadd : Finset.Iio n = {nm1} ∪ Finset.Iio nm1 := by
    grind

  have hhh : (∑ i < n, i) = nm1 + (∑ i < nm1, i) := by

    grind

  rw [hprev] at hhh
  rw [hhh]
  have hn : n = nm1 + 1 := by
    exact Eq.symm (Nat.succ_pred_eq_of_ne_zero hnzero)

  rw [hn]
  have h1 : (nm1+1)*nm1 = nm1^2 + nm1 := by
    noncomm_ring

  set nm2 := nm1-1
  have hnm2 : nm1 = nm2 + 1 := by
    exact Eq.symm (Nat.sub_add_cancel hnm1pos)
  have h2 : nm1*(nm1-1) = nm1^2 - nm1 := by
    rw [hnm2]
    grind

  rw [h1, h2]
  rw [hnm2]
  grind


variable (p q : Prop)

example (hp : p ∧ (¬ p)) : 0 = 1 := by

  tauto
