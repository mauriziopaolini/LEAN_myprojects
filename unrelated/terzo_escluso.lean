open Classical
theorem em (p : Prop) : p ∨ ¬p := by
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩

  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV

  have not_uv_or_p : u ≠ v ∨ p := by
    match u_def, v_def with
    | Or.inr h, _ => exact Or.inr h
    | _, Or.inr h => exact Or.inr h
    | Or.inl hut, Or.inl hvf =>
      apply Or.inl
      simp [hvf, hut]

  have p_implies_uv : p → u = v :=
  fun hp =>
  have hpred : U = V :=
    funext fun x =>
      have hl : (x = True ∨ p) → (x = False ∨ p) :=
        fun _ => Or.inr hp
      have hr : (x = False ∨ p) → (x = True ∨ p) :=
        fun _ => Or.inr hp
      show (x = True ∨ p) = (x = False ∨ p) from
        propext (Iff.intro hl hr)
  have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
    rw [hpred]; intros; rfl
  show u = v from h₀ _ _

  match not_uv_or_p with
  | Or.inl hne =>
    exact Or.inr (mt p_implies_uv hne)
  | Or.inr h   =>
    exact Or.inl h
