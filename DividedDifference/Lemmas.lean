/-
-/

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import DividedDifference.Defs

open Set

variable {f : ℝ → ℝ} {a b : ℝ} {x : ℕ → ℝ} {n p q : ℕ}

lemma strictMono_leq_n (n : ℕ) (x : ℕ → ℝ) (h_ordered_nodes: ∀ k < n, x k < x (k+1)) (hq : q ≤ n) (hp : p < q) :
  x p < x q := by

  cases hhq:q
  case zero =>
    rw [hhq] at hp
    tauto
  case succ qq =>
    rw [hhq] at hq hp
    clear hhq
    induction hhqq:qq generalizing qq
    case zero =>
      rw [hhqq] at hp hq
      have hpzero : p = 0 := by
        linarith
      rw [hpzero]
      simp
      have n_gt_0 : 0 < n := by
        simp at hq
        linarith
      specialize h_ordered_nodes 0 n_gt_0
      simp at h_ordered_nodes
      exact h_ordered_nodes
    case succ qqq hqqq =>
      rw [hhqq] at hp
      by_cases hhhh : p < qqq + 1
      rw [hhqq] at hq
      have hp' : qqq + 1 ≤ n := by
        linarith
      have qqq' : qqq = qqq := by
        tauto
      have hq' : qqq + 1 < n := by
        linarith
      specialize h_ordered_nodes (qqq+1) hq'
      specialize hqqq qqq hhhh hp' qqq'
      linarith

      have hhhh' : qqq ≤ p := by
        linarith

      have hp' : p = qqq + 1 := by
        linarith
      rw [← hp']
      rw [hhqq] at hq
      have pltn : p < n := by
        linarith
      specialize h_ordered_nodes p pltn
      exact h_ordered_nodes

lemma multiRolle (hn_ne_0 : n ≠ 0) (hab : a < b)
  (hx0 : a ≤ x 0) (hxn : x n ≤ b)
  (h_ordered_nodes: ∀ k < n, (x k) < x (k+1))
  (hfc : ContinuousOn f (Icc a b))
  (zerof : ∀ k ≤ n, f (x k) = 0)
  : ∃ (y : ℕ → ℝ) , ∀ k < n , ((deriv f) (y k) = 0 ∧ (y k > x k) ∧ (y k < x (k+1))) := by
    cases h:n
    case zero =>
      rw [h] at hn_ne_0
      exfalso
      tauto
    case succ m =>
      rw [h] at hn_ne_0 hxn h_ordered_nodes zerof

      clear h
      induction hm:m generalizing m x a
      case zero =>
        rw [hm] at hxn
        rw [zero_add]
        have hx0x1 : x 0 < x 1 := h_ordered_nodes 0 (by linarith)
        have hfI : f (x 0) = f (x 1) := by
          rw [zerof 0 (by linarith)]
          rw [zerof 1 (by linarith)]
        have hfcx0x1 : ContinuousOn f (Icc (x 0) (x 1)) := by
          apply ContinuousOn.mono hfc
          apply Icc_subset_Icc hx0 hxn
          --exact hx0
          --exact hxn

        let ⟨c, cmem, hc⟩ := exists_deriv_eq_zero hx0x1 hfcx0x1 hfI

        have cgtx0 : x 0 < c := by
          exact cmem.left
        have cltx1 : c < x 1 := by
          exact cmem.right
        have cgta : c > a := by
          apply lt_of_le_of_lt at hx0
          exact hx0 cgtx0
        have cltb : c < b := by
          apply lt_of_lt_of_le at cltx1
          exact cltx1 hxn
        have cmemab : c ∈ Ioo a b := by
          exact ⟨cgta, cltb⟩
        use fun k => if k = 0 then c else 0
        intro hk
        cases hk

        case succ kdum =>
          simp

        case zero =>
          simp; use hc

      case succ mm ih =>
        have hx0x1 : x 0 < x 1 := by
          specialize h_ordered_nodes 0
          rw [zero_add] at h_ordered_nodes
          have h : 0 < m + 1 := by simp
          specialize h_ordered_nodes h
          exact h_ordered_nodes
        have hfI : f (x 0) = f (x 1) := by
          rw [zerof 0 (by linarith)]
          rw [zerof 1 (by linarith)]

        have hfcx0x1 : ContinuousOn f (Icc (x 0) (x 1)) := by
          apply ContinuousOn.mono hfc
          apply Icc_subset_Icc hx0
          have hx1ltxmp1 : x 1 < x (m+1) := by
            apply strictMono_leq_n (m + 1) x h_ordered_nodes
            simp
            simp
            rw [hm]; simp

          rw [hm] at h_ordered_nodes
          clear ih
          linarith

        let ⟨c, cmem, hc⟩ := exists_deriv_eq_zero hx0x1 hfcx0x1 hfI

        let x_cdr := pop_vec x

        rw [hm] at h_ordered_nodes zerof

        unfold Ioo at cmem
        have hcinx0x1: x 0 < c ∧ c < x 1 := by
          exact cmem
        have hcltb : c < b := by
          clear ih
          have cltx1 : c < x 1 := by
            --have h: x 0 < c ∧ c < x 1 := by
            --  exact cmem
            exact hcinx0x1.2

          have x1ltxmmp2 : x 1 < x (mm+2) := by
            apply strictMono_leq_n (mm + 2) x h_ordered_nodes
            simp
            simp

          have xmmp2leb : x (mm+2) ≤ b := by
            rw [hm] at hxn; rw [add_assoc] at hxn
            simp at hxn; exact hxn

          linarith

        have halexcdr0 : c ≤ x_cdr 0 := by
          have x_cdr0eqx1 : x_cdr 0 = x 1 := by

            apply pop_vec_v 0 x x_cdr
            tauto

          clear ih
          rw [x_cdr0eqx1]
          have h : c < x 1 := by
            exact hcinx0x1.2
          linarith

        have hfccb : ContinuousOn f (Icc c b) := by
          clear ih
          apply ContinuousOn.mono hfc
          apply Icc_subset_Icc
          have hx0ltc : x 0 < c := by
            apply hcinx0x1.1
          linarith
          linarith

        have zerosf' : ∀ k ≤ mm + 1, f (x_cdr k) = 0 := by
          clear ih
          intro k hk
          have x_cdrkeqxkp1 : x_cdr k = x (k+1) := by

            apply pop_vec_v k x x_cdr
            tauto

          rw [x_cdrkeqxkp1]
          specialize zerof (k + 1)
          apply zerof
          linarith

        have h_ordered_nodes' : ∀ k < mm + 1, x_cdr k < x_cdr (k + 1) := by
          clear ih
          intro k
          have ht1 : x_cdr k = x (k+1) := by
            apply pop_vec_v k x x_cdr
            tauto
          have ht2 : x_cdr (k+1) = x (k+2) := by
            apply pop_vec_v (k+1) x x_cdr
            tauto
          rw [ht1]; rw [ht2]
          specialize h_ordered_nodes (k+1)
          intro hkltmmp1
          have hkp1ltmmp1p1 : k + 1 < mm + 1 + 1 := by
            linarith
          specialize h_ordered_nodes hkp1ltmmp1p1
          rw [add_assoc] at h_ordered_nodes
          simp at h_ordered_nodes
          exact h_ordered_nodes

        have h_xcdrmmp1lexmmp2 : x_cdr (mm + 1) = x (mm + 2) := by
          apply pop_vec_v (mm + 1) x x_cdr
          tauto

        have h_xcdrmmp1leb : x_cdr (mm + 1) ≤ b := by
          clear ih
          rw [h_xcdrmmp1lexmmp2]
          rw [hm] at hxn
          rw [add_assoc] at hxn
          simp at hxn
          exact hxn

        have hn_ne_0' : mm + 1 ≠ 0 := by
          simp

        have hmm_eq_mm : mm = mm := by
          rfl

        specialize ih hcltb halexcdr0 hfccb mm zerosf' h_ordered_nodes' h_xcdrmmp1leb hn_ne_0' -- hmm_eq_mm

        specialize ih hmm_eq_mm

        obtain ⟨y_tail, hy_tail⟩ := ih

        let y := push_vec c y_tail
        use y
        intro k hk
        cases hk':k
        case zero =>
          have hfirst : y 0 = c := by
            apply push_vec_v0 y_tail y c
            rfl

          constructor
          rw [hfirst]
          exact hc

          rw [hfirst]
          simp

          exact cmem

        case succ kk =>
          have hrest : y (kk + 1) = y_tail kk := by
            apply push_vec_v kk y_tail y c
            rfl

          rw [hrest]
          specialize hy_tail kk
          rw [hk'] at hk
          have hk'' : kk < mm + 1 := by
            linarith

          constructor
          specialize hy_tail hk''
          exact hy_tail.1

          tauto


lemma regularderiv (f : ℝ → ℝ) (a b : ℝ) (mm : ℕ) (hf : ContDiffOn ℝ (mm + 1) f (Ioo a b)) :
    ContDiffOn ℝ (mm) (deriv f) (Ioo a b) := by

  have hopen : IsOpen (Ioo a b) := by
    apply isOpen_Ioo

  apply ContDiffOn.deriv_of_isOpen hf hopen

  norm_cast

lemma f_eq_g_on_ab (f : ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ)
    (same : ∀ z ∈ (Ioo a b), f z = g z) (hcontf : ContinuousOn f (Ioo a b)) :
    ContinuousOn g (Ioo a b) := by

  have hopen : IsOpen (Ioo a b) := by
    apply isOpen_Ioo
  -- Since $f(z) = g(z)$ for all $z \in (a, b)$, and $f$ is continuous on $(a, b)$, it follows that $g$ is also continuous on $(a, b)$ by the fact that continuity is preserved under equality of functions.
  have h_cont_g : ContinuousOn (fun z => f z) (Set.Ioo a b) → ContinuousOn (fun z => g z) (Set.Ioo a b) := by
    -- Since $f(z) = g(z)$ for all $z \in (a, b)$, and $f$ is continuous on $(a, b)$, it follows that $g$ is also continuous on $(a, b)$ by the fact that equality of functions preserves continuity.
    intros hcontf_eq; exact (by
    -- Since $f$ and $g$ are equal on $(a, b)$, and $f$ is continuous on $(a, b)$, it follows that $g$ is also continuous on $(a, b)$ by the fact that equality of functions preserves continuity.
    apply ContinuousOn.congr hcontf_eq; exact fun z hz => same z hz ▸ rfl;);
  -- Apply the fact that if two functions are equal on an open set and one is continuous, then the other is also continuous.
  apply h_cont_g hcontf

lemma regularderiv0 (f : ℝ → ℝ) (a b : ℝ) (s : ℕ) (hf : ContDiffOn ℝ (s + 1) f (Ioo a b)) :
    ContinuousOn (deriv f) (Ioo a b) := by

  have ffp1 : ContinuousOn (iteratedDerivWithin 1 f (Ioo a b)) (Ioo a b) := by
    apply ContDiffOn.continuousOn_iteratedDerivWithin hf
    simp
    apply uniqueDiffOn_Ioo
  have ffp : ContinuousOn (derivWithin f (Ioo a b)) (Ioo a b) := by
    rw [iteratedDerivWithin_one] at ffp1
    exact ffp1
  have hopen : IsOpen (Ioo a b) := by
    apply isOpen_Ioo
  have same_in_ab : ∀ z ∈ (Ioo a b), (deriv f) z = (derivWithin f (Ioo a b)) z := by
    intro z hz
    rw [derivWithin_of_isOpen hopen]
    exact hz
  have same_in_ab' : ∀ z ∈ (Ioo a b), (derivWithin f (Ioo a b)) z = (deriv f) z := by
    intro z hz
    rw [derivWithin_of_isOpen hopen]
    exact hz

  apply f_eq_g_on_ab (derivWithin f (Ioo a b)) (deriv f)
  exact same_in_ab'
  exact ffp
