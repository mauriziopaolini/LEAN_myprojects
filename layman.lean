/-
  WHAT IS LEAN?
  A modern, statically typed programming language and proof assistant.
  It is used for both general-purpose programming and formal
  mathematical verification.

  Aggiungerei: E' una versione moderna dei "principia matematica" di
  Whitehead e Russell, ma (molto) più umanamente maneggevole
 -/

/-
  Questo è un commento.  In LEAN è possibile utilizzare simboli
  matematici come

        ∈ ∀ ∃ → ...

  Gli editor predisposti permettono
  di immettere tali caratteri utilizzando sequenze di tasti che ricordano
  i comandi LATEX.
  In effetti LEAN (L∃∀N) cerca di mediare il rigore di un formalismo
  logico che garantisce la correttezza cercando di mimare il linguaggio
  tipico di una dimostrazione matematica
-/
-- anche questo è un commento

/-
  Gli 'import' seguenti servono ad avere a disposizione
  una parte della libreria 'mathlib', un 'corpus' di matematica
  verificata con LEAN e sviluppato dalla community
  -/
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic

/-
  Vogliamo che da qui in avanti x sia un numero reale e n sia
  un numero naturale
-/
variable (x : ℝ) (n : ℕ)

/-
  Vediamo un primo semplice esempio di dimostrazione (Kevin Buzzard)

  Vogliamo dimostrare che "Non è vero che 'se x al quadrato meno
  tre x + 2 uguale a zero, allora x uguale a 1'"
  Spiegare 'example' vs 'theorem' vs 'lemma'
 -/


example : x^2 - 3*x + 2 = 0 → x = 1 := by

  sorry


example : ¬ 1 = 2 := by
  decide


example : ¬ ∀ x : ℝ, (x^2 - 3*x + 2 = 0 → x = 1) := by

  sorry












  -- push_neg
  -- use 2
  -- clear x
  -- constructor
  -- grind

  -- norm_num

/- trabocchetti... -/

#check 2 - 3
#eval 2 - 3
#eval (2:ℤ) - (3:ℤ)
#eval (2:ℝ) - (3:ℝ)


/-
 Nel prossimo esempio non c'è verso di completare la dimostrazione...
 Perché?
 -/

example : ¬ ∀ n, (n^2 - 3*n + 2 = 0 → n = 1) := by

  push_neg
  use 2
  constructor
  -- grind
  sorry

  decide

/-
 In effetti riusciamo a dimostrare la negazione
 dell'affermazione precedente
 -/

example : ∀ n, (n^2 - 3*n + 2 = 0 → n = 1) := by

  norm_num


#eval 2^2 - 3*2 + 2
#eval 4 - 6
#eval (2:ℤ) - (3:ℤ)
#eval (2:ℝ) - (3:ℝ)

















/-
Putnam 2017 A1:

Let S be the smallest set of positive integers such that
 a) 2 ∈ S,
 b) n^2 ∈ S → n ∈ S,
 c) n ∈ S → (n+5)^2 ∈ S.
Which positive integers are not in S?
 -/

def isputnam (S : Set ℕ) : Prop :=
  (∀ n : ℕ, n^2 ∈ S → n ∈ S) ∧ (∀ n ∈ S, (n+5)^2 ∈ S)

lemma emptyset_is_putnam : isputnam ∅ := by
  unfold isputnam
  exact ⟨fun n a => a, fun n a => a⟩

example : isputnam (Set.univ : Set ℕ) := by
  unfold isputnam
  norm_num

def S_target : Set ℕ := {n : ℕ | n ≥ 2 ∧ (n % 5 ≠ 0)}

lemma S_target_is_putnam : (isputnam S_target) := by

  unfold S_target isputnam
  constructor
  intro n hn
  have h2leqn : 2 ≤ n := by

    have hnsq : 2 ≤ n^2 := by
      simp_all only [ge_iff_le, ne_eq, Set.mem_setOf_eq]

    by_contra hcontra
    have hnlt2 : n < 2 := by
      simp_all only
       [ge_iff_le, ne_eq, Set.mem_setOf_eq, true_and, not_le]

    have hneq0or1 : n = 0 ∨ n = 1 := by
      omega
    obtain hneq0|hneq1 := hneq0or1
    grind
    grind

  have nneq5 : ¬ (5 ∣ n) := by
    have hnsqndiv5 : ¬ (5 ∣ n^2) := by
      grind
    contrapose hnsqndiv5
    have hp : Prime 5 := by
      decide
    refine Dvd.dvd.pow hnsqndiv5 ?_
    norm_num

  grind

  intro n hn
  let m := n + 5
  have hmneq5 : m % 5 ≠ 0 := by
    grind

  let msq := m^2
  have hmsqnew5 : msq % 5 ≠ 0 := by
    by_contra hmsqmultiple
    have hmsqk5 : 5 ∣ msq := by
      exact Nat.dvd_of_mod_eq_zero hmsqmultiple

    have hmeq5 : 5 ∣ m := by
      have hp : Prime 5 := by
        decide
      exact Prime.dvd_of_dvd_pow hp hmsqk5

    omega

  grind


-- #check S_target


lemma nplus5 {n : ℕ} {S : Set ℕ} (h1 : isputnam S) (h2 : n ∈ S) : (n+5)∈ S := by
  let nplus5 := n+5
  let m := (nplus5)^2
  unfold isputnam at h1
  obtain ⟨hfirst, hsecond⟩ := h1
  have h3 : m ∈ S := by
    grind

  specialize hfirst nplus5
  tauto

lemma nplusk5'' {n m : ℕ} {S : Set ℕ} (h1 : isputnam S)
    (h2 : n ∈ S) (h3 : m ≥ n) (h4 : (m-n) % 5 = 0)
    : m ∈ S := by

  let k := (m-n)/5
  have hm : m = n + k*5 := by
    omega

  induction hk:k generalizing n k
  case zero =>
    rw [hk] at hm
    have hmeqn : m = n := by
      trivial

    simp_all only [zero_mul, add_zero, ge_iff_le, le_refl, tsub_self, Nat.zero_mod]

  case succ kk s =>
    have hnplus5 : n + 5 ∈ S := by
      exact nplus5 h1 h2

    --rw [hm] at s
    --specialize s hnplus5
    --specialize s kk
    sorry

lemma nplusk5 {n : ℕ} {S : Set ℕ} (h1 : isputnam S) (h2 : n ∈ S) :
    ∀ k : ℕ, n + k*5 ∈ S := by
  intro k
  induction hk:k generalizing n k
  case zero =>
    trivial

  case succ kk s =>
    have nplus5 : n + 5 ∈ S := by
      exact nplus5 h1 h2
    specialize s nplus5
    specialize s kk
    grind

lemma nplusk5' {n : ℕ} {S : Set ℕ} {k : ℕ} (h1 : isputnam S) (h2 : n ∈ S) :
    n + k*5 ∈ S := by

  exact nplusk5 h1 h2 k

/-
  Dimostriamo che se S contiene un numero congruo a 4, allora contiene
  anche un numero congruo a 1
-/

theorem putnam41 {S : Set ℕ} (hclosed : isputnam S) (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 4)
    : ∃ m, m ≥ 2 ∧ m % 5 = 1 := by

  let k := n/5
  let m := (n + 5)^2
  have heuclid : n = 5*k + 4 := by
    omega

  have hsq : (n + 5)^2 ∈ S := by
    unfold isputnam at hclosed
    simp_all only [ge_iff_le]

  have hsq1 : m % 5 = 1 := by
    rw [heuclid] at hsq
    grind

  have hsq2 : m ≥ 2 := by
    grind

  use m


/-
  Dimostriamo che se S contiene un numero congruo a 2, allora contiene
  anche un numero congruo a 1
-/
theorem putnam21 {S : Set ℕ} (hclosed : isputnam S) (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 2)
    : ∃ m, m ≥ 2 ∧ m % 5 = 1 := by

  unfold isputnam at hclosed
  let k := n/5
  let m := (n + 5)^2
  have heuclid : n = 5*k + 2 := by
    omega

  have hsq : (n + 5)^2 ∈ S := by
    simp_all only [ge_iff_le]

  have hsq1 : m % 5 = 4 := by
    rw [heuclid] at hsq
    grind

  have hsq2 : m ≥ 2 := by
    grind

  have hm : m ∈ S ∧ m ≥ 2 ∧ m % 5 = 4 := by
    trivial

  apply putnam41 m hclosed hm


/-
  Dimostriamo che se S contiene un numero congruo a 3, allora contiene
  anche un numero congruo a 1
-/
theorem putnam31 {S : Set ℕ} (hclosed : isputnam S) (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 3)
    : ∃ m, m ≥ 2 ∧ m % 5 = 1 := by

  unfold isputnam at hclosed
  let k := n/5
  let m := (n + 5)^2
  have heuclid : n = 5*k + 3 := by
    omega

  have hsq : (n + 5)^2 ∈ S := by
    simp_all only [ge_iff_le]

  have hsq1 : m % 5 = 4 := by
    rw [heuclid] at hsq
    grind

  have hsq2 : m ≥ 2 := by
    grind

  have hm : m ∈ S ∧ m ≥ 2 ∧ m % 5 = 4 := by
    trivial

  apply putnam41 m hclosed hm

lemma nsqincreasing (n : ℕ) (hn: n ≥ 2) : n^2 ≥ n + 2 := by
  let nm2 := n - 2
  have hnx : n = nm2 + 2 := by grind

  have hnm1 : nm2 + 1 ≥ 1 := by
    norm_num

  have hhn : (nm2+2)*(nm2+1) ≥ 2 := by
    exact Nat.le_of_ble_eq_true rfl

  rw [hnx]
  grind

/-
  Dimostriamo che se S contiene un numero congruo a 1, allora per ogni m ≥ 2 congruo a 1
  S contiene m
-/
theorem putnam11 {S : Set ℕ} {n m : ℕ} (hclosed : isputnam S) (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 1)
    (hm : m ≥ 2) (hm2 : m % 5 = 1) : m ∈ S := by

  --intro m hm hm2
  obtain ⟨hn1, hn2, hn3⟩ := hn

  -- unfold isputnam at hclosed
  by_cases hm0 : m ≥ n
  let k := (m-n)/5
  have hm1 : m = n + k*5 := by
    omega

  have hhh : n + k*5 ∈ S := by
    exact nplusk5 hclosed hn1 k

  rw [hm1]
  trivial

  let msq := m^2

  have hmsq : msq % 5 = 1 := by

    let k := m / 5
    have hm3 : m = k*5 + 1 := by
      omega

    show m^2 % 5 = 1
    rw [hm3]
    grind

  have hmsqincr : m^2 ≥ m + 2 := by
    exact nsqincreasing m hm

  have hmsq0 : m^2 ≥ 2 := by
    grind

  have hmsqinS : msq ∈ S := by
    have hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 1 := by
      trivial

    have hsqincreasing : msq > m := by
      grind

    have hdecr : n - msq < n - m := by
      grind

    have hngtm : n > m := by
      grind

    let newdelta := n - m^2
    --apply putnam11 hclosed hn hmsq0 hmsq termination_by n -
    apply putnam11 hclosed hn hmsq0 hmsq
    --sorry

  unfold isputnam at hclosed
  tauto



theorem putnam {S : Set ℕ} {n : ℕ} (hclosed : isputnam S) (hn : n ∈ S ∧ n ≥ 2 ∧ ¬ 5 ∣ n)
    : S_target ⊆ S := by

  unfold isputnam at hclosed
  unfold S_target
  let k := n/5
  let r := n % 5
  have heuclid : n = 5*k + r := by
    exact Eq.symm (Nat.div_add_mod n 5)
  have hrlt6 : r < 5 := by
    omega

  by_cases hr0 : r = 0
  grind
  by_cases hr1 : r = 1
  sorry
  by_cases hr2 : r = 2
  sorry
  by_cases hr3 : r = 3
  sorry
  by_cases hr4 : r = 4
  sorry

  grind


theorem putnam0 {S : Set ℕ}
              (hclosed : isputnam S)
              (htwo : 2 ∈ S) :
              7 ∈ S := by

  exact nplus5 hclosed htwo
