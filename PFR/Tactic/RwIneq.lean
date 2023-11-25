import Mathlib.Data.Complex.Exponential

/-! # Rewriting in inequalities using `gcongr`

The file defines an inequality rewriting tactic powered by the `gcongr` tactic.

Given an inequality assumption `bound : r a b` where `r` is an inequality relation, and an
expression `e : s x y`  where `s` is an inequality relation, `rw_ineq [e] at bound`
will rewrite `x` to `y` in `bound` in the sense that `bound` will become `r a c` where `c` is
obtained from `b` by replacing `x` by `y` in every function argument (here function includes
arithmetical operations).

```
open Real

example (x y z w u : ℝ) (bound : x * exp y ≤ z + exp w) (h : w ≤ u) :  x * exp y ≤ z + exp u := by
  rw_ineq h at bound
  exact bound
```

The example above is implemented as

```
example (x y z w u : ℝ) (bound : x * exp y ≤ z + exp w) (h : w ≤ u) :  x * exp y ≤ z + exp u := by
  replace bound : x * exp y ≤ z + exp u := by
    have : z + exp w ≤ z + exp u := by gcongr
    exact Trans.trans bound this
  exact bound
```

As with `rw`, the combination `rw_ineq ... ; assumption` can be abreviated to `rwa_ineq`.

Rewriting from right to left is also supported. Given an inequality assumption `bound : r a b` and
an expression `e : s x y`, `rw_ineq [← e] at bound` will rewrite `y` to `x` in `bound` in the sense
that `bound` will become `r c b` where `c` is obtained from `a` by replacing `y` by `x` in every
function argument.

The following two snippets are equivalent are illustrate what is automated by the tactic in this
case.
```
example (x y z w u : ℝ) (bound : x * exp y ≤ z + 2*exp w) (h : u ≤ x) :
    u * exp y ≤ z + 2*exp w := by
  rw_ineq [← h] at bound
  exact bound

example (x y z w u : ℝ) (bound : x * exp y ≤ z + 2*exp w) (h : u ≤ x) :
    u * exp y ≤ z + 2*exp w := by
  replace bound : u * exp y ≤ z + 2*exp w := by
    have : u * exp y ≤ x * exp y := by gcongr
    exact Trans.trans this bound
  exact bound
```

Rewriting in the goal is also possible. Given an inequality goal `⊢ r a b` and an expression
`e : s x y`, `rw_ineq [e]` will rewrite `x` to `y` in the goal in the sense that it will become
`r c b` where `c` is obtained from `a` by replacing `x` by `y` in every function argument.

The following example show how this is implemented, and also show how to do several rewriting in
one command. As with ordinary `rw`, the tactic state update depending on the cursor position
inside the sequence of expressions in square brackets.
```
example {a c : ℕ} (hc : a < c) : 2 * a ≤ 3 * c  := by
  rw_ineq [show 2 ≤ 3 by norm_num, hc]

example {a c : ℕ} (hc : a < c) : 2 * a ≤ 3 * c  := by
  have := show 2 ≤ 3 by norm_num
  have : 2 * a ≤ 3 * a := by gcongr
  apply @Trans.trans _ _ _ LE.le LE.le LE.le _ _ _ _ this
  try linarith only [this]

  have : 3 * a ≤ 3 * c := by gcongr
  apply @Trans.trans _ _ _ LE.le LE.le LE.le _ _ _ _ this
  try linarith only [this]
```

**TODO**: The tactic currently assume all inequalities are `≤` or `<`. We should preprocess
`≥` and `>` (and change the meaning of right to left rewriting accordingly).
-/



open Lean Meta Elab Term Tactic

initialize registerTraceClass `rw_ineq

/-- Given an expression of the shape `r a b` or a meta-variable whose type has this shape,
return `some (r, a, b)`, otherwise returns `none`. -/
partial def Lean.Expr.relInfo? : Expr → MetaM (Option (Expr × Expr × Expr))
| .mvar m => do Lean.Expr.relInfo? (← m.getType'')
| e@(_) =>  if e.getAppNumArgs < 2 then
    return none
  else
    return some (e.appFn!.appFn!, e.appFn!.appArg!, e.appArg!)

/-- Returns a version of `target` where any occurence of `old` as a function argument has
been replaced by `new`. Comparison with `old` is up to defEq. -/
def Lean.Expr.subst (target old new : Expr) : MetaM Expr := do
  if ← isDefEq target old then
    return new
  else
    match target with
    | Expr.app fn arg    => return (Expr.app (← fn.subst old new) (← arg.subst old new))
    | _                  => return target

/-- Given expressions `orig : r a b` and `subst : s x y` for some relations
`r` and `s`, build the expression `r b c` where `c` is obtained from `b` by replacing
any occurence of `x` in a function application argument by `y`. -/
def Lean.Expr.substInRel (orig subst : Expr) : MetaM (Option Expr) := do
  let some (relo, _lo, ro) := ← orig.relInfo? | return none
  let some (_rels, ls, rs) := ← subst.relInfo? | return none
  return some (← mkAppM' relo #[ro, (← ro.subst ls rs)])

/-- Given expressions `orig : r a b` and `subst : s x y` for some relations
`r` and `s`, build the expression `r a c` where `c` is obtained from `a` by replacing
any occurence of `x` in a function application argument by `y`. -/
def Lean.Expr.substInRel' (orig subst : Expr) : MetaM (Option Expr) := do
  let some (relo, lo, _ro) := ← orig.relInfo? | return none
  let some (_rels, ls, rs) := ← subst.relInfo? | return none
  return some (← mkAppM' relo #[lo, (← lo.subst ls rs)])

/-- Given expressions `orig : r a b` and `subst : s x y` for some relations
`r` and `s`, build the expression `r c a` where `c` is obtained from `a` by replacing
any occurence of `y` in a function application argument by `x`. -/
def Lean.Expr.substInRelRev (orig subst : Expr) : MetaM (Option Expr) := do
  let some (relo, lo, _ro) := ← orig.relInfo? | return none
  let some (_rels, ls, rs) := ← subst.relInfo? | return none
  return some (← mkAppM' relo #[(← lo.subst rs ls), lo])

/-- Given expressions `orig : r a b` and `subst : s x y` for some relations
`r` and `s`, build the expression `r c b` where `c` is obtained from `b` by replacing
any occurence of `y` in a function application argument by `x`. -/
def Lean.Expr.substInRelRev' (orig subst : Expr) : MetaM (Option Expr) := do
  let some (relo, _lo, ro) := ← orig.relInfo? | return none
  let some (_rels, ls, rs) := ← subst.relInfo? | return none
  return some (← mkAppM' relo #[(← ro.subst rs ls),ro ])

def gcongrDefaultDischarger (g : MVarId) : MetaM PUnit :=Term.TermElabM.run' do
  let [] ← Tactic.run g <| evalTactic (Unhygienic.run `(tactic| gcongr_discharger)) | failure

/-- Rewrite in the relation assumption `h : r a b` using `subst : s x y` to produce `h : r a c`
where `c` is obtained from `b` by replacing any occurence of `x` in a function application argument
by `y`. This new relation `h` is proven from `trans h h'` where `h' : r b c` is proven by `gcongr`
using the list of given identifiers for newly introduced variables.
Returns the list of new goals. -/
def Lean.MVarId.rwIneq (g : MVarId) (fvarId : FVarId) (substPrf : Expr) (rev : Bool)
    (names : List (TSyntax ``binderIdent)) : MetaM (List MVarId) := do
  g.withContext do
  let subst := (← Lean.instantiateMVars (← inferType substPrf)).consumeMData
  let decl ← (← getLCtx).find? fvarId
  let substFun := if rev then Lean.Expr.substInRelRev else Lean.Expr.substInRel
  let some newIneq ← substFun decl.type.consumeMData subst
    | throwError "Could not create the new relation."
  trace[rw_ineq] "New inequality: {← ppExpr newIneq}"
  let g ← if substPrf.isFVar then pure g else do
    let (_, g) ← g.note (← mkFreshUserName `providedRel) substPrf
    pure g
  g.withContext do
  let mvar ← mkFreshExprMVar newIneq
  let (success, _, newGoals) ← mvar.mvarId!.gcongr none names gcongrDefaultDischarger
  if success then
    let g ← g.clear decl.fvarId
    let transArgs := if rev then #[mvar, .fvar decl.fvarId] else #[.fvar decl.fvarId, mvar]
    let (_, newGoal) ← g.note decl.userName (← mkAppM `Trans.trans transArgs)
    return newGoal::newGoals.toList
  else
    throwError "The `gcongr` tactic called by `rw_ineq` failed."

/-- Version of `Trans.trans` with argument order swapped. This is a hack to make it easier
to use `MVarId.apply`. -/
lemma Trans.trans' {α β γ : Sort*} {r : α → β → Sort*}
  {s : β → γ → Sort*} {t : outParam (α → γ → Sort*)} [Trans r s t] {a : α} {b : β} {c : γ}
  (h : s b c) (h' : r a b) : t a c := Trans.trans h' h

deriving instance DecidableEq for MVarId

open Linarith in
/-- Rewrite in the relation target `⊢ r a b` using `subst : s x y` to reduce the goal to `h : r c b`
where `c` is obtained from `a` by replacing any occurence of `x` in a function application argument
by `y`. The old goal is proven from the new one using `trans h h'` where `h' : r b c` is proven by `gcongr`
using the list of given identifiers for newly introduced variables.
Returns the list of new goals. -/
def Lean.MVarId.rwIneqTgt (g : MVarId) (substPrf : Expr) (rev : Bool)
    (names : List (TSyntax ``binderIdent)) : MetaM (List MVarId) := do
  g.withContext do
  let subst := (← Lean.instantiateMVars (← inferType substPrf)).consumeMData
  let tgt := (← g.getType).consumeMData
  let some (_, tgtLHS, tgtRHS) ← tgt.relInfo?
    | throwError "The current goal is not a relation."
  let substFun := if rev then Lean.Expr.substInRelRev' else Lean.Expr.substInRel'
  let some newIneq ← substFun tgt subst
    | throwError "Could not create the new relation."
  trace[rw_ineq] "New inequality: {← ppExpr newIneq}"
  let (providedRelFVarId?, g) ← if substPrf.isFVar then pure (none, g) else do
    let intermediateName ← mkFreshUserName `providedRel
    let (providedRelFVarId, g) ← g.note intermediateName substPrf
    pure (some providedRelFVarId, g)
  g.withContext do
  let newIneqPrf ← mkFreshExprMVar newIneq
  let (success, _, newGCongrGoals) ← newIneqPrf.mvarId!.gcongr none names gcongrDefaultDischarger
  let newGCongrGoals := newGCongrGoals.toList
  if success then
    trace[rw_inew] "gcongr produced goals: {newGCongrGoals.map (·.name)}"
    let relExpr : Expr := mkAppN tgt.getAppFn tgt.getAppArgs[:2]
    let newGoal ← if let some fvarId := providedRelFVarId? then g.clear fvarId
      else pure g
    let transExpr ← if rev then
      mkAppOptM `Trans.trans' #[none, none, none, relExpr, none, none, none, tgtLHS, none, none,
        newIneqPrf]
    else
      mkAppOptM `Trans.trans #[none, none, none, none, relExpr, none, none, none, none, tgtRHS,
        newIneqPrf]
    let newerGoals ← newGoal.apply transExpr
    trace[rw_ineq] "apply produced goals: {newerGoals.map (·.name)}"
    let mut goals : List MVarId := []
    for goal in (newerGoals ++ newGCongrGoals).dedup do
      try
        commitIfNoEx <| do
          trace[rw_ineq] s!"Will try linarith on {← ppExpr <| ← goal.getType} with only " ++
            s!"{← ppExpr <| ← inferType substPrf}"
          goal.withContext do
            linarith true [substPrf] {preprocessors := defaultPreprocessors} goal
          trace[rw_ineq]  "Success!"
      catch e =>
        trace[rw_ineq] "Failed on {goal.name}: {← e.toMessageData.format}."
        goals := goal::goals
    return goals
  else
    throwError "The `gcongr` tactic called by `rw_ineq` failed."

open Lean Parser Tactic

syntax withClause := " with " (colGt Lean.binderIdent)?

/-- `rw_ineq [e] at h` rewrites in the relation assumption `bound : r a b` using `e : s x y` to
replace `bound` with `r a c` where `c` is obtained from `b` by replacing any occurence of `x` in a
function application argument by `y`. This may generate new goals including new objects that can
be named using the `with` clause.

```
open Real

example (x y z w u : ℝ) (bound : x * exp y ≤ z + exp w) (h : w ≤ u) :  x * exp y ≤ z + exp u := by
  rw_ineq h at bound
  exact bound
```

Given an inequality goal `⊢ r a b` and an expression `e : s x y`, `rw_ineq [e]` will rewrite `x` to
`y` in the goal in the sense that it will become `r c b` where `c` is obtained from `a` by replacing
`x` by `y` in every function argument.

```
example {a c : ℕ} (hc : a < c) : 2 * a ≤ 3 * c  := by
  rw_ineq [show 2 ≤ 3 by norm_num, hc]
```

The variant `rwa_ineq` calls `assumption` after `rw_ineq`.
-/
elab tok:"rw_ineq" rules:rwRuleSeq loc:(location)? withArg:(withClause)? : tactic =>
  withMainContext do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := fun h ↦ do
      -- Note: we use the username to track the local assumption being rewritten and whose FVarId
      -- changes with each rewrite.
      let userName := (← (← getLCtx).find? h).userName
      withRWRulesSeq tok rules fun symm term ↦ do
        let mainGoal ← getMainGoal
        mainGoal.withContext do
        let fvar := (← (← getLCtx).findFromUserName? userName).fvarId
        let substPrf ← Lean.Elab.Term.elabTerm term none
        let names := match withArg with
        | some Arg =>(Arg.raw[1].getArgs.map TSyntax.mk).toList
        | none => []
        replaceMainGoal (← mainGoal.rwIneq fvar substPrf symm names))
    (atTarget := withMainContext do
      withRWRulesSeq tok rules fun symm term ↦ do
        let mainGoal ← getMainGoal
        mainGoal.withContext do
        let substPrf ← Lean.Elab.Term.elabTerm term none
        let names := match withArg with
        | some Arg =>(Arg.raw[1].getArgs.map TSyntax.mk).toList
        | none => []
        let goals ← mainGoal.rwIneqTgt substPrf symm names
        replaceMainGoal goals)
    (failed := fun _ ↦ throwError "rw_ineq failed")

/-- `rw_ineq [e] at h` rewrites in the relation assumption `bound : r a b` using `e : s x y` to
replace `bound` with `r a c` where `c` is obtained from `b` by replacing any occurence of `x` in a
function application argument by `y`. This may generate new goals including new objects that can
be named using the `with` clause.

```
open Real

example (x y z w u : ℝ) (bound : x * exp y ≤ z + exp w) (h : w ≤ u) :  x * exp y ≤ z + exp u := by
  rw_ineq h at bound
  exact bound
```

Given an inequality goal `⊢ r a b` and an expression `e : s x y`, `rw_ineq [e]` will rewrite `x` to
`y` in the goal in the sense that it will become `r c b` where `c` is obtained from `a` by replacing
`x` by `y` in every function argument.

```
example {a c : ℕ} (hc : a < c) : 2 * a ≤ 3 * c  := by
  rw_ineq [show 2 ≤ 3 by norm_num, hc]
```

The variant `rwa_ineq` calls `assumption` after `rw_ineq`.
-/
macro "rwa_ineq " rws:rwRuleSeq loc:(location)? withArg:(withClause)? : tactic =>
  `(tactic| (rw_ineq $rws:rwRuleSeq $[$loc:location]? $[$withArg]?; assumption))

open Real

example (x y z w u : ℝ) (bound : x * exp y ≤ z + 2*exp w) (h : w ≤ u) :
    x * exp y ≤ z + 2*exp u := by
  rw_ineq [h] at bound
  exact bound

example (x y z w u : ℝ) (bound : x * exp y < z + 2*exp w) (h : w < u) :
    x * exp y < z + 2*exp u := by
  rwa_ineq [h] at bound

example (x y z w u : ℝ) (bound : x * exp y ≤ z + 2*exp w) (h : u ≤ x) :
    u * exp y ≤ z + 2*exp w := by
  rw_ineq [← h] at bound
  exact bound

example (x y z w u : ℝ) (bound : x * exp y ≤ z + 2*exp w) (h : u ≤ x) :
    u * exp y ≤ z + 2*exp w := by
  replace bound : u * exp y ≤ z + 2*exp w := by
    have : u * exp y ≤ x * exp y := by gcongr
    exact Trans.trans this bound
  exact bound


-- Test where a side condition is not automatically discharged.
example (x y z w u : ℝ) (bound : x * exp y < z + x^2*exp w) (h : w < u) (hx : 2*x > 2) :
    x * exp y < z + x^2*exp u := by
  rwa_ineq [h] at bound
  apply pow_pos
  linarith

example {a b c d : ℝ} (bound : a + b ≤ c + d) (h : c ≤ 2) (k : 1 ≤ a) : 1 + b ≤ 2 + d := by
  rwa_ineq [h, ← k] at bound

example {a b : ℕ} (h : a ≤ 2 * b) : a ≤ 3 * b  := by
  rwa_ineq [show 2 ≤ 3 by norm_num] at h

example {a b : ℝ} (hb : 0 < b) (h: a ≤ 2 * b) : a ≤ 3 * b  := by
  have test : (2 : ℝ) ≤ 3 := by norm_num
  rwa_ineq [test] at h

example {a c : ℕ} (hc : a < c) : 2 * a ≤ 3 * c  := by
  rw_ineq [show 2 ≤ 3 by norm_num, hc]

example {a c : ℕ} (hc : a < c) : 2 * a ≤ 3 * c  := by
  rw_ineq [← hc]

example {n : ℕ} (bound : n ≤ 5) (h: 5 ≤ 10): n ≤ 10 := by
  have h' := (show 5 ≤ 10 by norm_num)
  rw_ineq [h] at bound
  assumption

example {n : ℕ} (bound : n ≤ 5) : n ≤ 10 := by
  have h' : 5 ≤ 10 := by norm_num
  rw_ineq [h'] at bound
  assumption

example {n : ℕ} (bound : n ≤ 5) : n ≤ 10 := by
  rw_ineq [show 5 ≤ 10 by norm_num] at bound
  assumption

example {n : ℕ} (bound : n ≤ 5) : n ≤ 10 := by
  have h' := (show 5 ≤ 10 by norm_num)
  rw_ineq [h'] at bound
  assumption
