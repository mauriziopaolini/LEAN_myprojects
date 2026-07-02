/-
 -/

import Mathlib

variable (x : ℝ) (i : ℕ)


theorem gauss (n : ℕ) (hnpos : n > 0): (∑ i < n, i) = n*(n-1)/2 := by

  by_cases hnzero : n = 0
  linarith

  by_cases hnone : n = 1
  have hf : Finset.Iio n = {0} := by
    grind

  rw [hf, hnone]
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
    apply gauss nm1 hnm1pos

  have hadd : Finset.Iio n = {nm1} ∪ Finset.Iio nm1 := by
    grind

  have hhh : (∑ i < n, i) = nm1 + (∑ i < nm1, i) := by

    grind

  rw [hprev] at hhh
  rw [hhh]
  have hn : n = nm1 + 1 := by
    exact (Nat.sub_eq_iff_eq_add hnpos).mp rfl

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



lemma lemgauss (n : ℕ) : (∑ i < n, (i+1)) = n*(n+1)/2 := by

  by_cases hzero : n = 0
  rw [hzero]
  have hempty : Finset.Iio 0 = ∅ := by
    norm_num

  rw [hempty]

  grind

  have hngt0 : 0 < n := by
    positivity

  set nm1 := n - 1
  have hmp1 : n = nm1 + 1 := by
    exact (Nat.sub_eq_iff_eq_add hngt0).mp rfl

  have hprev : (∑ i < nm1, (i+1)) = nm1*(nm1+1)/2 := by


    apply lemgauss nm1

  have hh : (∑ i < n, (i+1)) = (∑ i < nm1, (i+1)) + n := by
    have hfinset : Finset.Iio n = {nm1} ∪ Finset.Iio nm1 := by
      grind

    rw [hfinset]
    have hnotin : ¬ nm1 ∈ Finset.Iio nm1 := by
      norm_num

    have hhh : ∑ i ∈ Finset.Iio n, (i+1) =
            (∑ i ∈ {nm1}, (i+1)) +
            (∑ i ∈ Finset.Iio nm1, (i+1)) := by
      grind

    rw [←hfinset]
    rw [hhh]

    have hfirst : ∑ i ∈ {nm1}, (i+1) = n := by
      simp_all only [Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, lt_add_iff_pos_left,
        Order.lt_add_one_iff, zero_le, Finset.singleton_union, Finset.Iio_insert, Finset.mem_Iio, lt_self_iff_false,
        Finset.sum_singleton]

    rw [hfirst]
    ring

  rw [hh]
  rw [hprev]
  rw [hmp1]
  grind
