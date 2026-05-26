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



example : ¬ ∀ n, (n^2 - 3*n + 2 = 0 → n = 1) := by
  push_neg
  use 2
  constructor
  -- grind
  sorry

  norm_num

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

def isputnam (S : Set ℕ ) : Prop :=
  (∀ n : ℕ, n^2 ∈ S → n ∈ S) ∧ (∀ n ∈ S, (n+5)^2 ∈ S)

example : isputnam ∅ := by
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
  have ngeq2 : 2 ≤ n := by

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


#check S_target

example {r : ℕ} (n : ℕ) (hr : r = n % 5) : r ≤ 4 := by
  sorry


lemma nplus5 {n : ℕ} {S : Set ℕ} (h1 : isputnam S) (h2 : n ∈ S) : (n+5)∈ S := by
  let nplus5 := n+5
  let m := (nplus5)^2
  unfold isputnam at h1
  obtain ⟨hfirst, hsecond⟩ := h1
  have h3 : m ∈ S := by
    grind

  specialize hfirst nplus5
  tauto

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


theorem putnam0 {S : Set ℕ}
              (hclosed : isputnam S)
              (htwo : 2 ∈ S) :
              7 ∈ S := by

  exact nplus5 hclosed htwo
