/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d2159c14-8113-48c5-a79a-951fede680ca

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma row1d_chain_spec {n : Nat} (ngt0 : n > 0) (coeffs : List.Vector ℤ n)
    (xin yout xout yin : ℕ → ℤ)
    (h : ROW1D ngt0 (List.Vector.ofFn (fun i : Fin n => FIR_TAP (coeffs.get i)))
         (xin, yout) (xout, yin)) :
    (∀ t, xout t = semisystolic_chain coeffs xin n t) ∧
    (∀ t, yout t = yin t +
      Finset.univ.sum fun i : Fin n => semisystolic_chain coeffs xin (i.val + 1) t)

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Ruby


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
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

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
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

namespace Ruby

def fir_spec {n : Nat}
    (coeffs : List.Vector Nat n) (x : ℕ → ℤ) : ℕ → ℤ :=
  fun t => Finset.univ.sum fun i : Fin n =>
    if t < i.val then 0 else coeffs.get i * x (t - i.val)

def ADD_INT : Rel ((ℕ → ℤ) × (ℕ → ℤ)) (ℕ → ℤ) :=
  fun ab o => ∀t, o t = ab.1 t + ab.2 t

def MUL_INT : Rel ((ℕ → ℤ) × (ℕ → ℤ)) (ℕ → ℤ) :=
  fun ab o => ∀t, o t = ab.1 t * ab.2 t

def ROW1D {α : Type} {n : Nat} : n > 0 → List.Vector (Rel α α) n → Rel α α :=
  fun _ v => match n with
  | 1 => v.get ⟨0, Nat.zero_lt_one⟩
  | n + 2 => v.head ⨾ ROW1D (Nat.succ_pos n) v.tail

def FIR_TAP : ℤ → Rel ((ℕ → ℤ) × (ℕ → ℤ)) ((ℕ → ℤ) × (ℕ → ℤ)) := fun coief (xin, yout) (xout, yin) =>
  ∃ xin', DELAY (0 : ℤ) xin xin' ∧
          MUL_INT (xin', coief) xout ∧
          ADD_INT (xout, yin) yout

def ZERO (_ : ℕ) : ℤ  := 0

def SEMISYSTOLIC_FIR {n : Nat} (ngt0 : n > 0) (coeffs : List.Vector ℤ n) :
    Rel (ℕ → ℤ) (ℕ → ℤ) := fun xin yout =>
  let taps := List.Vector.ofFn (fun i : Fin n => FIR_TAP (coeffs.get i))
  ∃ xout, ROW1D ngt0 taps (xin, yout) (xout, ZERO)

/-- Intermediate "x" signal at position i in the semisystolic FIR chain.
    Position 0 is the original input. Position i+1 is the delayed and
    coefficient-scaled version of position i. -/
def semisystolic_chain {n : Nat} (coeffs : List.Vector ℤ n) (xin : ℕ → ℤ) :
    (i : Nat) → ℕ → ℤ
  | 0 => xin
  | i + 1 => fun t =>
    if t = 0 then 0
    else if h : i < n then coeffs.get ⟨i, h⟩ * semisystolic_chain coeffs xin i (t - 1)
    else 0

/-- Specification for the semisystolic pipelined FIR filter.
    The output at time t is the sum of the chain signals at positions
    1 through n, where each chain signal is the delayed, cumulatively
    coefficient-scaled input. -/
def semisystolic_fir_spec {n : Nat} (coeffs : List.Vector ℤ n) (xin : ℕ → ℤ) : ℕ → ℤ :=
  fun t => Finset.univ.sum fun i : Fin n =>
    semisystolic_chain coeffs xin (i.val + 1) t

/-- A single FIR_TAP with coefficient c relates the x output to the
    delayed and scaled input, and the y output to the sum of the
    x output and the y input from the next stage. -/
lemma fir_tap_spec (c : ℤ) (xin yout xout yin : ℕ → ℤ)
    (h : FIR_TAP c (xin, yout) (xout, yin)) :
    (∀ t, xout t = if t = 0 then 0 else c * xin (t - 1)) ∧
    (∀ t, yout t = xout t + yin t) := by
  obtain ⟨xin', h_delay, h_mul, h_add⟩ := h
  dsimp [DELAY, MUL_INT, ADD_INT] at h_delay h_mul h_add
  constructor
  · intro t
    by_cases ht : t = 0
    · subst ht
      have hd : xin' 0 = 0 := by have := h_delay 0; rwa [if_pos rfl] at this
      rw [if_pos rfl, h_mul 0, hd, zero_mul]
    · have hd : xin' t = xin (t - 1) := by have := h_delay t; rwa [if_neg ht] at this
      rw [if_neg ht, h_mul t, hd, mul_comm]
  · exact h_add

/-- The ROW1D chain of FIR_TAPs produces x and y signals matching
    the semisystolic_chain specification: the threaded x signal at the
    end equals semisystolic_chain at position n, and the y output equals
    the y input plus the sum of chain signals at positions 1 through n. -/
lemma row1d_chain_spec {n : Nat} (ngt0 : n > 0) (coeffs : List.Vector ℤ n)
    (xin yout xout yin : ℕ → ℤ)
    (h : ROW1D ngt0 (List.Vector.ofFn (fun i : Fin n => FIR_TAP (coeffs.get i)))
         (xin, yout) (xout, yin)) :
    (∀ t, xout t = semisystolic_chain coeffs xin n t) ∧
    (∀ t, yout t = yin t +
      Finset.univ.sum fun i : Fin n => semisystolic_chain coeffs xin (i.val + 1) t) := by
  revert h yout xout yin xin coeffs ngt0 n; (
  intros n ngt0 coeffs xin yout xout yin h; induction' n with n ih generalizing xin yout xout yin <;> simp_all +decide [ Fin.sum_univ_succ ] ;
  · contradiction;
  · rcases n with ( _ | n ) <;> simp_all +decide [ List.ofFn_succ ];
    · obtain ⟨ xin', hxin', hxout, hyout ⟩ := h;
      simp_all +decide [ Ruby.MUL_INT, Ruby.ADD_INT, Ruby.semisystolic_chain ];
      simp_all +decide [ mul_comm, Ruby.DELAY ];
      grind +ring;
    · -- Let's simplify the goal using the definition of `ROW1D`.
      obtain ⟨xout', yout', hxout', hyout'⟩ : ∃ xout' yout', Ruby.FIR_TAP (coeffs.get ⟨0, by linarith⟩) (xin, yout) (xout', yout') ∧ Ruby.ROW1D (Nat.succ_pos n) (List.Vector.ofFn (fun i : Fin (n + 1) => Ruby.FIR_TAP (coeffs.get ⟨i.val + 1, by linarith [Fin.is_lt i]⟩))) (xout', yout') (xout, yin) := by
        have h_row1d : Ruby.ROW1D (Nat.succ_pos (n + 1)) (List.Vector.ofFn (fun i : Fin (n + 2) => Ruby.FIR_TAP (coeffs.get i))) (xin, yout) (xout, yin) → ∃ xout' yout', Ruby.FIR_TAP (coeffs.get ⟨0, by linarith⟩) (xin, yout) (xout', yout') ∧ Ruby.ROW1D (Nat.succ_pos n) (List.Vector.ofFn (fun i : Fin (n + 1) => Ruby.FIR_TAP (coeffs.get ⟨i.val + 1, by linarith [Fin.is_lt i]⟩))) (xout', yout') (xout, yin) := by
          intro h_row1d
          obtain ⟨xout', yout', hxout', hyout'⟩ : ∃ xout' yout', Ruby.FIR_TAP (coeffs.get ⟨0, by linarith⟩) (xin, yout) (xout', yout') ∧ Ruby.ROW1D (Nat.succ_pos n) (List.Vector.ofFn (fun i : Fin (n + 1) => Ruby.FIR_TAP (coeffs.get ⟨i.val + 1, by linarith [Fin.is_lt i]⟩))) (xout', yout') (xout, yin) := by
            have h_row1d_def : Ruby.ROW1D (Nat.succ_pos (n + 1)) (List.Vector.ofFn (fun i : Fin (n + 2) => Ruby.FIR_TAP (coeffs.get i))) = Ruby.FIR_TAP (coeffs.get ⟨0, by linarith⟩) ⨾ Ruby.ROW1D (Nat.succ_pos n) (List.Vector.ofFn (fun i : Fin (n + 1) => Ruby.FIR_TAP (coeffs.get ⟨i.val + 1, by linarith [Fin.is_lt i]⟩))) := by
              exact?
            exact h_row1d_def ▸ h_row1d |> fun ⟨ x, hx ⟩ => ⟨ _, _, hx.1, hx.2 ⟩ ;
          generalize_proofs at *; aesop;
        generalize_proofs at *; aesop;
      have := fir_tap_spec ( coeffs.get ⟨ 0, by linarith ⟩ ) xin yout xout' yout' hxout';
      specialize ih ( List.Vector.ofFn fun i : Fin ( n + 1 ) => coeffs.get ⟨ i.val + 1, by linarith [ Fin.is_lt i ] ⟩ ) xout' yout' xout yin ; simp_all +decide [ Fin.sum_univ_succ ] ;
      -- By definition of `semisystolic_chain`, we can rewrite the goal in terms of the chain signals.
      have h_chain : ∀ i : Fin (n + 1), ∀ t, Ruby.semisystolic_chain (List.Vector.ofFn fun (i : Fin (n + 1)) => coeffs.get ⟨(↑i : ℕ) + 1, by linarith [ Fin.is_lt i ] ⟩) xout' (i.val + 1) t = Ruby.semisystolic_chain coeffs xin (i.val + 2) t := by
        intro i t; induction' i using Fin.inductionOn with i IH generalizing t; simp +decide [ *, Ruby.semisystolic_chain ] ;
        simp +decide [ *, Ruby.semisystolic_chain ] at IH ⊢;
        specialize IH ( t - 1 ) ; rcases t with ( _ | _ | t ) <;> simp +decide [ * ] at IH ⊢ ;
        grind;
      refine' ⟨ fun t => _, fun t => _ ⟩ <;> simp_all +decide [ Fin.forall_fin_succ, Fin.sum_univ_succ ] ; ring!;
      · by_cases hn : n = 0 <;> simp_all +decide [ add_comm, add_left_comm, add_assoc ];
        convert h_chain.2 ⟨ n - 1, Nat.sub_lt ( Nat.pos_of_ne_zero hn ) zero_lt_one ⟩ t using 1 <;> cases n <;> trivial;
      · rw [ show Ruby.semisystolic_chain coeffs xin 1 t = if t = 0 then 0 else coeffs.head * xin ( t - 1 ) from ?_ ] ; ring!;
        -- By definition of `Ruby.semisystolic_chain`, we know that for `i = 1`, the chain signal is the coefficient times the delayed input.
        simp [Ruby.semisystolic_chain] at *);

/-- The semisystolic FIR circuit is correct: for any input signal xin,
    if SEMISYSTOLIC_FIR relates xin to yout, then yout agrees pointwise
    with the specification semisystolic_fir_spec. -/
theorem semisystolic_fir_correct {n : Nat} (ngt0 : n > 0) (coeffs : List.Vector ℤ n)
    (xin yout : ℕ → ℤ) (h : SEMISYSTOLIC_FIR ngt0 coeffs xin yout) :
    ∀ t, yout t = semisystolic_fir_spec coeffs xin t := by
  unfold SEMISYSTOLIC_FIR at h
  obtain ⟨xout, h_row⟩ := h
  have ⟨_, h_y⟩ := row1d_chain_spec ngt0 coeffs xin yout xout ZERO h_row
  intro t
  rw [h_y t]
  simp [ZERO, semisystolic_fir_spec]

end Ruby