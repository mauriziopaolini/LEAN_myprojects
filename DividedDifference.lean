-- This module serves as the root of the `DividedDifference` library.
-- Import modules here that should be built as part of the library.

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Lagrange
import DividedDifference.HigherOrderRolle

import Batteries.Tactic.GeneralizeProofs

open Set

variable {f : ℝ → ℝ} {a b : ℝ}

/-
There are four versions of the "order_n_Rolle".  It generally state that
a sufficiently regular function that vanishes at n+1 distinct nodes in [a,b]
admits a point within the set of nodes where its n-th derivative vanishes.

- order_n_Rolle_V

espects the n+1 nodes as the first values of a sequence x : ℕ → ℝ in strictly
increasing order, then the resulting point c satisfies c ∈ ( x 0, x n )

- order_n_Rolle_L

same as above, but the nodes are given as the elements of a List ℝ, still they
are required to be given in increasing order

- order_n_Rolle_F

The nodes are indicated as a Finset ℝ, hence they are unordered.  The resulting c is
shown to belong to the interior of the Convex hull of the set of nodes.

- order_n_Rolle_F_weak

same as above, but the resulting c is only shown to belong to the open interval (a,b).
This could be useful if one does not want to use the definition of
"intOfHull" (the interior of the convex hull of the set of nodes) which might be
inconvenient to manage.  Still of course the user can take a and b as the minimum
and maximum of the nodes and still recovere the stronger result

- order_n_Rolle_unorderedL (obsoleted)

same as above, but the nodes are not required to be in increasing order.  Of course
they must be mutually disjoint

- order_n_Rolle_unorderedL_weak (obsoleted)

weaker version of above, where the resulting point c is only guaranteed to
be in (a,b).
-/

/-
  nodes organized in a vector x : ℕ → ℝ
-/

theorem order_n_Rolle_V {x : ℕ → ℝ} (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hx0 : a ≤ x 0) (hxn : x n ≤ b)
    (h_ordered_nodes: ∀ k < n, (x k) < x (k+1))
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ k ≤ n, f (x k) = 0)
    : ∃ c ∈ Ioo (x 0) (x n), iteratedDeriv n f c = 0 := by

  apply extRolle n hn_ne_0 hab hx0 hxn h_ordered_nodes hfc hf zerof

/-
  In this variant the nodes are still ordered, but organized in a List
  structure
-/

theorem order_n_Rolle_L {listnodes : List ℝ} (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : listnodes.length = n + 1)
    (hx0 : a ≤ listnodes.getD 0 0) (hxn : listnodes.getD n 0 ≤ b)
    (h_ordered_nodes: ∀ k < n, (listnodes.getD k 0) < (listnodes.getD (k+1) 0))
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ listnodes, f x = 0)
    : ∃ c ∈ Ioo (listnodes.getD 0 0) (listnodes.getD n 0), iteratedDeriv n f c = 0 := by

  apply extRolle_L n hn_ne_0 hab hcard hx0 hxn h_ordered_nodes hfc hf zerof


/-
Main result: there is c ∈ intOfHullS of the nodes, the nodes are given as a
list of n+1 distict points in [a,b]
-/

theorem order_n_Rolle_F (n : ℕ) (hn_ne_0 : n ≠ 0)
    (nodes : Finset ℝ)
    (hcard : nodes.card = n + 1)
    (hab : a < b)
    (nodesinab : ∀ x ∈ nodes, x ∈ Icc a b)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n - 1) f (Ioo a b))
    (zerof : ∀ x ∈ nodes, f x = 0)
    : ∃ c ∈ intOfHull nodes, iteratedDeriv n f c = 0 := by

  apply extRolle_F n hn_ne_0 nodes hcard hab nodesinab hfc hf zerof

/-
Weak version where we are satisfied with c ∈ (a,b)
we should prove this using the main theorem
-/

theorem order_n_Rolle_F_weak (n : ℕ) (hn_ne_0 : n ≠ 0) (nodes : Finset ℝ)
    (hcard : nodes.card = n + 1)
    (hab : a < b)
    (nodesinab : ∀ x ∈ nodes, x ∈ Icc a b)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n - 1) f (Ioo a b))
    (zerof : ∀ x ∈ nodes, f x = 0)
    : ∃ c ∈ Ioo a b, iteratedDeriv n f c = 0 := by

  apply extRolle_F_weak n hn_ne_0 nodes hcard hab nodesinab hfc hf zerof


/-
Main result: order n divided difference equals the nth derivative of f divided
by n!
-/


namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

lemma contdiffpol (n : ℕ) (p : Polynomial ℝ)
    : ContDiffOn ℝ n p.eval (Ioo a b) := by
  -- Since polynomials are infinitely differentiable, their nth derivative is also a polynomial, which is smooth. Therefore, the nth derivative is continuous on the interval.
  have h_poly_cont_diff : ContDiffOn ℝ ⊤ (fun x => p.eval x) (Set.Ioo a b) := by
    -- Since polynomials are infinitely differentiable, their evaluations are also infinitely differentiable.
    have h_poly_cont_diff : ∀ p : Polynomial ℝ, ContDiffOn ℝ ⊤ (fun x => p.eval x) (Set.Ioo a b) := by
      -- Since polynomials are infinitely differentiable, their evaluations are also infinitely differentiable. We can use the fact that the evaluation of a polynomial is a polynomial function, which is known to be infinitely differentiable.
      intro p
      have h_poly_cont_diff : ContDiff ℝ ⊤ (fun x => p.eval x) := by
        -- Since polynomials are infinitely differentiable, their evaluations are also infinitely differentiable. Therefore, the function p.eval is ContDiff ℝ ⊤.
        have h_poly_cont_diff : ∀ p : Polynomial ℝ, ContDiff ℝ ⊤ (fun x => p.eval x) := by
          -- Since polynomials are analytic, we can apply the theorem that states that analytic functions are ContDiffOn.
          have h_poly_analytic : ∀ p : Polynomial ℝ, AnalyticOn ℝ (fun x => p.eval x) Set.univ := by
            intro p
            have h_poly_analytic : AnalyticOn ℝ (fun x => p.eval x) Set.univ := by
              have h_poly_analytic : ∀ x : ℝ, AnalyticAt ℝ (fun x => p.eval x) x := by
                intro x
                have h_poly_analytic : AnalyticAt ℝ (fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i) x := by
                  fun_prop
                generalize_proofs at *;
                simpa only [ Polynomial.eval_eq_sum_range ] using h_poly_analytic
              exact?
            exact h_poly_analytic;
          exact fun p => by simpa using h_poly_analytic p |> AnalyticOn.contDiff;
        exact h_poly_cont_diff p
        skip
      exact h_poly_cont_diff.contDiffOn;
    exact h_poly_cont_diff p;
  -- Since ⊤ is greater than or equal to any natural number n, if the function is ContDiffOn ℝ ⊤, then it's also ContDiffOn ℝ n.
  apply ContDiffOn.of_le; exact h_poly_cont_diff; exact le_top


theorem divided_difference_eq_deriv_n (n : ℕ) (hn_ne_0 : n ≠ 0) (nodes : Finset ℝ)
    (hab : a < b)
    (hcard : nodes.card = n + 1)
    (nodesinab : ∀ x ∈ nodes, x ∈ Icc a b)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ n f (Ioo a b))
    : ∃ c ∈ intOfHull nodes, divided_difference f nodes = (iteratedDeriv n f c)/(Nat.factorial n) := by

  let p := Lagrange.interpolate nodes my_id f
  let E := f - p.eval

  have zeroE : ∀ x ∈ nodes, E x = 0 := by
    have hinterp : ∀ x ∈ nodes, p.eval x = f x := by
      have hvs : Set.InjOn my_id nodes := by
        exact Function.Injective.injOn fun ⦃a₁ a₂⦄ a => a

      intro x hx
      apply Lagrange.eval_interpolate_at_node f hvs hx

    aesop

  have hpc : ContinuousOn p.eval (Icc a b) := by
    exact Polynomial.continuousOn_aeval p

  have hpmc : ContinuousOn (- p.eval) (Icc a b) := by
    simp_all only [ne_eq, mem_Icc, continuousOn_neg_iff]

  have hEc : ContinuousOn (f - p.eval) (Icc a b) := by
    apply ContinuousOn.sub hfc hpc

  have hp : ContDiffOn ℝ n p.eval (Ioo a b) := by
    apply contdiffpol n p

  have hE : ContDiffOn ℝ n (f - p.eval) (Ioo a b) := by
    apply ContDiffOn.sub hf hp

  have hE' : ContDiffOn ℝ (n-1) (f - p.eval) (Ioo a b) := by
    sorry

  have exists_c : ∃ c ∈ intOfHull nodes, iteratedDeriv n E c = 0 := by
    apply order_n_Rolle_F n hn_ne_0 nodes hcard hab nodesinab hEc hE' zeroE

  obtain ⟨c, hc1, hc2⟩ := exists_c
  use c
  constructor
  exact hc1

  let p_deriv_n := iteratedDeriv n p.eval

  have contdiff_f : ContDiffAt ℝ n f c := by
    sorry

  have contdiff_p : ContDiffAt ℝ n p.eval c := by
    sorry

  have hderivs : (iteratedDeriv n f c) = (iteratedDeriv n E c) + (p_deriv_n c) := by
    --apply iteratedDeriv_add contdiff_f contdiff_p
    sorry

  have p_deriv_n_val : p_deriv_n c = (Nat.factorial n) * (divided_difference f nodes) := by
    sorry

  field_simp
  rw [hderivs,hc2,zero_add,p_deriv_n_val]
  ring



/-
Obsoleted: Main result: there is c ∈ intOfHull of the nodes, the nodes are given as a
list of n+1 distict points in [a,b]
-/

variable {lnodes : List ℝ}

theorem order_n_Rolle_unorderedL (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : lnodes.length = n + 1)
    (hx0 : ∀ x ∈ lnodes, a ≤ x) (hxn : ∀ x ∈ lnodes, x ≤ b)
    (h_distinct_nodes : ∀ j ≤ n, ∀ i < j, lnodes.getD i 0 ≠ lnodes.getD j 0)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ lnodes, f x = 0)
    : ∃ c ∈ intOfHullL lnodes, iteratedDeriv n f c = 0 := by

  apply extRolle_unorderedL n hn_ne_0 hab hcard hx0 hxn h_distinct_nodes hfc hf zerof


/-
Weak version where we are satisfied with c ∈ (a,b)
we should prove this using the main theorem
-/

theorem order_n_Rolle_unorderedL_weak (n:ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : lnodes.length = n + 1)
    (hx0 : ∀ x ∈ lnodes, a ≤ x) (hxn : ∀ x ∈ lnodes, x ≤ b)
    (h_distinct_nodes : ∀ j ≤ n, ∀ i < j, lnodes.getD i 0 ≠ lnodes.getD j 0)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    (zerof : ∀ x ∈ lnodes, f x = 0)
    : ∃ c ∈ Ioo a b, iteratedDeriv n f c = 0 := by

  apply extRolle_unorderedL_weak n hn_ne_0 hab hcard hx0 hxn h_distinct_nodes hfc hf zerof


/- Lagrange interpolation: given a finset `s : Finset ι`, a nodal map `v : ι → F` injective on
`s` and a value function `r : ι → F`, `interpolate s v r` is the unique
polynomial of degree `< #s` that takes value `r i` on `v i` for all `i` in `s`. -/

/-
def interpolate (s : Finset ι) (v : ι → F) : (ι → F) →ₗ[F] F[X] where
  toFun r := ∑ i ∈ s, C (r i) * Lagrange.basis s v i
  map_add' f g := by
    simp_rw [← Finset.sum_add_distrib]
    have h : (fun x => C (f x) * Lagrange.basis s v x + C (g x) * Lagrange.basis s v x) =
    (fun x => C ((f + g) x) * Lagrange.basis s v x) := by
      simp_rw [← add_mul, ← C_add, Pi.add_apply]
    rw [h]
  map_smul' c f := by
    simp_rw [Finset.smul_sum, C_mul', smul_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
-/

open Polynomial
namespace Polynomial
open Function Fintype
open scoped Finset

/-
def divided_difference (f : ℝ → ℝ) (lnodes : List ℝ) : ℝ :=
  0

theorem divided_difference_eq_nth_deriv (n : ℕ) (hn_ne_0 : n ≠ 0) (hab : a < b)
    (hcard : lnodes.length = n + 1)
    (hx0 : ∀ x ∈ lnodes, a ≤ x) (hxn : ∀ x ∈ lnodes, x ≤ b)
    (h_distinct_nodes : ∀ j ≤ n, ∀ i < j, lnodes.getD i 0 ≠ lnodes.getD j 0)
    (hfc : ContinuousOn f (Icc a b))
    (hf : ContDiffOn ℝ (n-1) f (Ioo a b))
    : ∃ c ∈ Ioo a b, (divided_difference f lnodes) = iteratedDeriv n f c := by

  have hs : s = Finset (n+1)
  have hinterp : Lagrange.interpolate
  sorry


-/
