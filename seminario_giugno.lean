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
import Mathlib

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





example : ¬ ∀ x : ℝ, (x^2 - 3*x + 2 = 0 → x = 1) := by

  sorry











  --push_neg
  --use 2
  --clear x
  --constructor
  --swap
  --norm_num

  --grind





/-
 Nel prossimo esempio non c'è verso di completare la dimostrazione...
 Perché?
 -/

example : ¬ ∀ n, (3 - 3*n + n^2 = 1 → n = 1) := by

  push_neg
  use 2
  constructor
  swap
  norm_num

  -- grind
  sorry








/-
 In effetti riusciamo a dimostrare la negazione
 dell'affermazione precedente
 -/

example : ∀ n, (n^2 - 3*n + 2 = 0 → n = 1) := by
  norm_num





/- trabocchetti... -/

--#eval 2^2 - 3*2 + 2

--#check 2^2 - 3*2
--#eval 2^2 - 3*2
--#eval (2:ℤ)^2 - (3:ℤ)*2
--#eval (2:ℝ) - (3:ℝ)

















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
  norm_num

lemma univ_is_putnam : isputnam (Set.univ : Set ℕ) := by
  unfold isputnam
  norm_num

/-
 NOTA: questo teorema non serve per risolvere il problema, ma mostra
 che viene definita una topologia per cui gli insiemi "isputnam" sono
 i chiusi

 Dimostriamo che gli insiemi "isputnam" sono chiusi rispetto
 all'intersezione
-/

open Set

theorem intersection_isputnam {I : Type*} (SS : I → Set ℕ)
    (h_inter : ∀ i : I, isputnam (SS i))
    : isputnam (⋂ i, SS i) := by

  unfold isputnam
  constructor
  intro n
  intro hS

  have hi : ∀ i, (n^2) ∈ SS i := by
    simp_all only [mem_iInter, implies_true]

  unfold isputnam at h_inter

  have hi1 : ∀ i, n ∈ SS i := by
    intro i
    have h_inter_dup := h_inter
    specialize h_inter_dup i
    obtain ⟨h_inter1, h_inter2⟩ := h_inter_dup
    specialize hi i
    specialize h_inter1 n
    specialize h_inter1 hi
    exact h_inter1

  simp_all only [mem_iInter, implies_true]

  unfold isputnam at h_inter
  intro n hS

  have hi : ∀ i, n ∈ SS i := by
    simp_all only [mem_iInter, implies_true]

  have hi1 : ∀ i, (n+5)^2 ∈ SS i := by
    intro i
    specialize h_inter i
    obtain ⟨h_inter1, h_inter2⟩ := h_inter
    specialize hi i
    specialize h_inter2 n
    specialize h_inter2 hi
    exact h_inter2

  simp_all only [mem_iInter, implies_true]




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
      simp_all only [ge_iff_le, ne_eq, Set.mem_setOf_eq, true_and, not_le]

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


/- ================================================== -/

lemma nplus5 {n : ℕ} {S : Set ℕ} (h1 : isputnam S) (h2 : n ∈ S) : (n+5)∈ S := by
  let nplus5 := n+5
  let m := (nplus5)^2
  unfold isputnam at h1
  obtain ⟨hfirst, hsecond⟩ := h1
  have h3 : m ∈ S := by
    grind

  specialize hfirst nplus5
  tauto

/- ================================================== -/

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


/-
  Dimostriamo che se S contiene un numero congruo a 4, allora contiene
  anche un numero congruo a 1 (mod 5)
-/
lemma putnam41 {S : Set ℕ} (hclosed : isputnam S)
    (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 4)
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



/- ================================================== -/

/-
  Dimostriamo che se S contiene un numero congruo a 2, allora contiene
  anche un numero congruo a 1 (mod 5)
-/
lemma putnam21 {S : Set ℕ} (hclosed : isputnam S) (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 2)
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



/- ================================================== -/

/-
  Dimostriamo che se S contiene un numero congruo a 3, allora contiene
  anche un numero congruo a 1
-/
lemma putnam31 {S : Set ℕ} (hclosed : isputnam S) (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 3)
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

/- ================================================================= -/

lemma nsqincreasing (n : ℕ) (hn: n ≥ 2) : n^2 ≥ n + 2 := by
  let nm2 := n - 2
  have hnx : n = nm2 + 2 := by grind

  have hnm1 : nm2 + 1 ≥ 1 := by
    norm_num

  have hhn : (nm2+2)*(nm2+1) ≥ 2 := by
    exact Nat.le_of_ble_eq_true rfl

  rw [hnx]
  grind

/- ================================================================= -/

/-
 ====> WOW!  Questo è il mio primo teorema RICORSIVO <====
 Dimostriamo che se n ∈ S, congruo a 1 (mod 5) e m è anch'esso congruo a 1 (mod 5)
 con 2 ≤ m < n, allora anche m ∈ S
 -/

lemma putnam11pre {S : Set ℕ} {n delta : ℕ} (hclosed : isputnam S)
    (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 1)
    (hdelta : delta > 0) (hdelta0 : delta ≤ n-2) (hdelta1 : 5 ∣ delta)
    : n-delta ∈ S := by

  let m := n - delta
  let k := (n-m)/5
  have hm0 : m ≥ 2 := by
    grind
  have hm1 : n = m + k*5 := by
    omega

  let msq := m^2

  have hmsq : msq % 5 = 1 := by

    let k := m / 5
    have hm3 : m = k*5 + 1 := by
      omega

    show m^2 % 5 = 1
    rw [hm3]
    grind

  have hmsqincr : m^2 ≥ m + 2 := by
    exact nsqincreasing m hm0

  have hmsq0 : m^2 ≥ 2 := by
    grind

  have hmsqinS : msq ∈ S := by
    obtain ⟨hn1, hn2, hn3⟩ := hn
    by_cases hsimple : msq ≥ n
    let k := (msq-n)/5
    have hmsq1 : msq = n + k*5 := by
      omega

    have hhh : n + k*5 ∈ S := by
      exact nplusk5 hclosed hn1 k

    rw [hmsq1]
    trivial

    have hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 1 := by
      trivial

    have hsqincreasing : msq > m := by
      grind

    have hdecr : n - msq < n - m := by
      grind

    have hngtm : n > m := by
      grind

    let newdelta := n - msq
    have hnewdelta : newdelta > 0 := by
      exact tsub_pos_iff_not_le.mpr hsimple
    have hnewdelta0 : newdelta ≤ n - 2 := by
      exact Nat.sub_le_sub_left hmsq0 n
    have hnewdelta1 : 5 ∣ newdelta := by
      omega

    have hhhh : msq = n - newdelta := by
      omega
    rw [hhhh]

    /- l'ipotesi che segue non sembra essere necessaria
       ma se proviamo a rimuoverla...
    -/
    have hdeltadecr : newdelta < delta := by
      omega
    --clear hdeltadecr
    apply putnam11pre hclosed hn hnewdelta hnewdelta0 hnewdelta1

  unfold isputnam at hclosed
  tauto

/- ================================================================= -/

/-
  Dimostriamo che se S contiene un numero congruo a 1, allora
  ∀ m ≥ 2 congruo a 1
  S contiene m
-/
lemma putnam_11 {S : Set ℕ} {n m : ℕ} (hclosed : isputnam S)
    (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 1)
    (hm : m ≥ 2) (hm2 : m % 5 = 1) : m ∈ S := by

  have hn1 : n ∈ S := by
    simp_all only [ge_iff_le]
  have hn2 : n ≥ 2 := by
    simp_all only [ge_iff_le, true_and]
  have hn3 : n % 5 = 1 := by
    simp_all only [ge_iff_le, true_and]
  --obtain ⟨hn1, hn2, hn3⟩ := hn
  by_cases htriv : m ≥ n
  let k := (m-n)/5
  have hm1 : m = n + k*5 := by
    omega

  have hhh : n + k*5 ∈ S := by
    exact nplusk5 hclosed hn1 k

  rw [hm1]
  trivial

  let delta := n-m

  have hdelta0 : delta ≤ n - 2 := by
    grind

  have hdelta1 : 5 ∣ delta := by
    omega

  have hhhh : m = n - delta := by
    omega
  rw [hhhh]

  have hdelta : delta > 0 := by
    simp_all only [ge_iff_le, and_self, not_le, tsub_lt_self_iff, gt_iff_lt]
  apply putnam11pre hclosed hn hdelta hdelta0 hdelta1



/- ================================================================= -/

/-
  Dimostriamo che se S contiene un numero non congruo a 0, allora per ogni m ≥ 2
  congruo a 1, m ∈ S
-/
lemma putnam_n1 {S : Set ℕ} {n m : ℕ} (hclosed : isputnam S)
    (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 ≠ 0)
    (hm : m ≥ 2) (hm2 : m % 5 = 1)
    : m ∈ S := by

  let r := n % 5
  let k := n / 5
  have hne : n = k*5 + r := by
    exact Eq.symm (Nat.div_add_mod' n 5)


  by_cases hr0 : r = 0
  grind


  by_cases hr1 : r = 1
  have hn' : n ∈ S ∧ n ≥ 2 ∧ n % 5 = 1 := by
    tauto
  apply putnam_11 hclosed hn' hm hm2


  by_cases hr4 : r = 4
  let nsq := (n+5)^2
  have hnsq2 : (n+5)^2 % 5 = 1 := by
    rw [hne]
    grind

  have hnsq : nsq ∈ S ∧ nsq ≥ 2 ∧ nsq % 5 = 1 := by
    constructor
    unfold isputnam at hclosed
    show (n + 5)^2 ∈ S
    obtain ⟨hclosed1, hclosed2⟩ := hclosed
    specialize hclosed2 n
    obtain ⟨hn1, hn2, hn3⟩ := hn
    tauto

    constructor
    show (n + 5)^2 ≥ 2
    grind

    show (n+5)^2 % 5 = 1
    gcongr


  apply putnam_11 hclosed hnsq hm hm2


  by_cases hr23 : r = 2 ∨ r = 3
  have hnsq : (n+5)^2 % 5 = 4 := by
    by_cases hr2 : r = 2
    rw [hne]
    rw [hr2]
    grind

    have hr3 : r = 3 := by
      simp_all only [ge_iff_le, Nat.mul_add_mod_self_right, ne_eq, false_or, Nat.succ_ne_self, not_false_eq_true]

    rw [hne]
    rw [hr3]
    grind

  have hnsqsq : ((n+5)^2 + 5)^2 % 5 = 1 := by
    let nsq5 := (n+5)^2
    show (nsq5 + 5)^2 % 5 = 1
    have hnsq5 : nsq5 % 5 = 4 := by
      gcongr
    have hnsq5plus : (nsq5 + 5) % 5 = 4 := by
      simp_all only [ge_iff_le, Nat.mul_add_mod_self_right, ne_eq, Nat.add_mod_right]
    let kk := (nsq5 + 5)/5
    have hnsqe : nsq5 + 5 = 5*kk + 4 := by
      grind
    rw [hnsqe]
    grind

  let nsqsq := ((n + 5)^2 + 5)^2
  have hnsqsq' : nsqsq ∈ S ∧ nsqsq ≥ 2 ∧ nsqsq % 5 = 1 := by
    constructor
    unfold isputnam at hclosed
    show ((n + 5)^2 + 5)^2 ∈ S
    obtain ⟨hclosed1, hclosed2⟩ := hclosed
    obtain ⟨hn1, hn2, hn3⟩ := hn
    have hmiddle : (n + 5)^2 ∈ S := by
      simp_all only [ge_iff_le, Nat.mul_add_mod_self_right, ne_eq]

    specialize hclosed2 ((n + 5)^2)
    tauto

    constructor
    grind

    gcongr


  apply putnam_11 hclosed hnsqsq' hm hm2

  omega


/- ================================================================= -/

/-
  Dimostriamo che se S contiene un numero NON congruo a 0, allora
  ∀ m ≥ 2 NON congruo a 0 → m ∈ S
-/
theorem putnam_nm {S : Set ℕ} {n m : ℕ} (hclosed : isputnam S)
    (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 ≠ 0)
    (hm : m ≥ 2) (hm2 : m % 5 ≠ 0)
    : m ∈ S := by

  let six := 6
  have hsix0 : six ≥ 2 := by decide
  have hsix1 : six % 5 = 1 := by decide
  have hsix : six ∈ S := by
    apply putnam_n1 hclosed hn hsix0 hsix1

  have hsix01 : six ∈ S ∧ six ≥ 2 ∧ six % 5 = 1 := by
    trivial

  by_cases hr1 : m % 5 = 1
  apply putnam_11 hclosed hsix01 hm hr1

  let msq := m^2
  by_cases hr4 : m % 5 = 4

  have hmsqinS : m^2 ∈ S := by
    have hmsq : m^2 ≥ 2 := by
      have hmsq' : m^2 ≥ m + 2 := by
        apply nsqincreasing m hm
      exact Nat.le_of_add_left_le hmsq'
    have hmsq1 : m^2 % 5 = 1 := by
      let k := m/5
      have hmeuclid : m = k*5 + 4 := by
        omega
      rw [hmeuclid]
      grind
    apply putnam_11 hclosed hsix01 hmsq hmsq1

  unfold isputnam at hclosed
  obtain ⟨hclosed1, hclosed2⟩ := hclosed
  specialize hclosed1 m
  specialize hclosed1 hmsqinS
  trivial

  have hm23 : m % 5 = 2 ∨ m % 5 = 3 := by
    grind

  have hmsqsq : (m^2)^2 ≥ 2 := by
    have hmsq : m^2 ≥ 2 := by
      have hmsq' : m^2 ≥ m + 2 := by
        apply nsqincreasing m hm
      exact Nat.le_of_add_left_le hmsq'
    have hmsqsq' : (m^2)^2 ≥ m^2 + 2 := by
      apply nsqincreasing (m^2) hmsq
    exact Nat.le_of_add_left_le hmsqsq'

  have hmsqsq1 : (m^2)^2 % 5 = 1 := by
    have hmsq1 : m^2 % 5 = 4 := by
      let k := m/5
      by_cases hm2 : m % 5 = 2
      have hmeuclid : m = k*5 + 2 := by
        omega
      rw [hmeuclid]
      grind
      have hm3 : m % 5 = 3 := by
        simp_all only [ge_iff_le, ne_eq, false_or,
                       Nat.succ_ne_self, not_false_eq_true]
      have hmeuclid : m = k*5 + 3 := by
        omega
      rw [hmeuclid]
      grind

    let k := m^2/5
    have hmeuclid : m^2 = k*5 + 4 := by
      omega
    rw [hmeuclid]
    grind

  have hmsqsqinS : (m^2)^2 ∈ S := by
    apply putnam_11 hclosed hsix01 hmsqsq hmsqsq1

  unfold isputnam at hclosed
  obtain ⟨hclosed1, hclosed2⟩ := hclosed
  have hclosed1copy : ∀ (n : ℕ), n ^ 2 ∈ S → n ∈ S := by
    finiteness
  specialize hclosed1 (m^2)
  specialize hclosed1 hmsqsqinS
  have hmsqinS : m^2 ∈ S := by
    trivial

  specialize hclosed1copy m
  specialize hclosed1copy hmsqinS
  exact hclosed1copy



/- ================================================================= -/

/-
  Per concludere come corollario dimostriamo che non ci sono insiemi "isputnam"
  stramente intermedi tra ∅ e S_target
-/
theorem putnam {S : Set ℕ} {n : ℕ} (hclosed : isputnam S)
    (hn : n ∈ S ∧ n ≥ 2 ∧ n % 5 ≠ 0)
    : S_target ⊆ S := by

  unfold isputnam at hclosed
  intro m
  by_cases hnot : m ∉ S_target
  tauto

  have hminStarget : m ∈ S_target := by
    simp_all only [ge_iff_le, ne_eq, not_not]

  clear hnot

  unfold S_target at hminStarget
  have hminS : m ∈ S := by
    have hm : m ≥ 2 := by
      simp_all only [ge_iff_le, ne_eq, Set.mem_setOf_eq]

    have hm2 : m % 5 ≠ 0 := by
      simp_all only [ge_iff_le, ne_eq,
                    Set.mem_setOf_eq, true_and, not_false_eq_true]

    apply putnam_nm hclosed hn hm hm2

  unfold S_target
  finiteness


/- ================================================================= -/
/- ================================================================= -/
/- ================================================================= -/

/- Rubato da XENA project -/
/- definizione originale:

/-- collatz n means the collatz conjecture is true for n -/
inductive collatz : ℕ → Prop
| coll0 : collatz 0
| coll1 : collatz 1
| coll_even : ∀ n : ℕ, collatz n → collatz (2 * n)
| coll_odd : ∀ n : ℕ , collatz (6 * n + 4) → collatz (2 * n + 1)

-/

inductive iscollatz : ℕ → Prop
| coll0 : iscollatz 0
| coll1 : iscollatz 1
| coll_even : ∀ n : ℕ, iscollatz n → iscollatz (2 * n)
| coll_odd : ∀ n : ℕ , iscollatz (6 * n + 4) → iscollatz (2 * n + 1)


def collatz_step (n : ℕ) : ℕ :=
  (1 - (n%2))*n/2 + (n%2)*(3*n + 1)

def collatz (n : ℕ) (k : ℕ) : ℕ :=
  Nat.iterate collatz_step k n
  --collatz_step^[k] n   -- sintassi alternativa

/- Iterate a function.
def Nat.iterate {α : Sort u} (op : α → α) : ℕ → α → α
  | 0, a => a
  | succ k, a => iterate op k (op a)
 -/

open Nat

def collatz_tr : ℕ → ℕ → ℕ
  | 0, a => a
  | succ k, a => collatz_tr k (collatz_step a)

def collatz' (n : ℕ) (k : ℕ) : ℕ :=
  collatz_tr k n


--#eval collatz 9 13

theorem collatz_even_ok (n : ℕ) (heven : n % 2 = 0)
    : collatz_step n = n/2 := by

  unfold collatz_step
  simp_all only [tsub_zero, one_mul, zero_mul, add_zero]


theorem collatz_odd_ok (n : ℕ) (hodd : n % 2 = 1)
    : collatz_step n = 3*n + 1 := by

  unfold collatz_step

  simp_all only [tsub_self, zero_mul, Nat.zero_div, one_mul, zero_add]

/- ================================================================= -/

def iscollatz' (n : ℕ) := ∃ C : ℕ, collatz n C = 1


theorem collatz_conjecture : ∀ n : ℕ, iscollatz n := by
  sorry


theorem collatz_conjecture_upto10 : ∀ m : ℕ, 0 < m ∧ m ≤ 10 → iscollatz' m := by

  unfold iscollatz'
  unfold collatz
  unfold collatz_step
  intro m

  by_cases hleq10 : 0 < m ∧ m ≤ 10
  swap
  tauto

  simp_all

  by_cases h0 : m = 1
  rw [h0]
  use 0
  decide

  by_cases h0 : m = 2
  rw [h0]
  use 1
  decide

  by_cases h0 : m = 4
  rw [h0]
  use 2
  decide

  by_cases h0 : m = 8
  rw [h0]
  use 3
  decide

  by_cases h0 : m = 5
  rw [h0]
  use 5
  decide

  by_cases h0 : m = 10
  rw [h0]
  use 6
  decide

  by_cases h0 : m = 7
  rw [h0]
  use 16
  decide

  by_cases h0 : m = 3
  rw [h0]
  use 7
  decide

  by_cases h0 : m = 6
  rw [h0]
  use 8
  decide

  by_cases h0 : m = 9
  rw [h0]
  use 19
  decide

  omega
