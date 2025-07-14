import Batteries
import Lean
import Qq
import TutorialAux.Init -- for Sections (5, 7)

/-!
# Tutorial: Writing `simp` from scratch

Content
(1) What `simp` does on proof term level?
(2) Filling implicit arguments
(3) Result structure
(4) Basic implementation
(5) Debugging with traces
(6) Implementing simp inside binders
(7) Collecting tagged lemmas
-/

open Lean Meta Elab Tactic Qq

/-
# (1) What `simp` does on proof term level?

Simp doesn't do all its equal rewrites in one go like `rw`.
Instead, it recursively dives into the term, and when
it combines two branches in which both terms got
updated, it uses
-/
#check congr

theorem simp_example (a b c : Nat) (f : Nat → Nat) (p : Nat → Prop)
    (h_eq  : ∀ x : Nat, f x = x) (h_finish : p (a + c + b + c + a + c)) :
    p (f a + c + f b + c + f a + c) := by
  simp only [h_eq]
  exact h_finish

#print simp_example

/-
This is much more messy than rw's but after prettification,
you could get the following proof term.
-/
example (a b c : Nat) (f : Nat → Nat) (p : Nat → Prop)
    (h_eq  : ∀ x : Nat, f x = x) (h_finish : p (a + c + b + c + a + c)) :
    p (f a + c + f b + c + f a + c) :=
  Eq.mpr
  (congrArg (fun X => p (X + c))
    (congr
      (congrArg (fun X => (X + c + ·))
        (congr
          (congrArg
            (fun X => (X + c + ·)) (h_eq a : f a = a)
            : (f a + c + ·) = (a + c + ·)
          )
          (h_eq b : f b = b)
          : f a + c + f b = a + c + b)
        : (f a + c + f b + c + ·) = (a + c + b + c + ·)
      )
      (h_eq a : f a = a)
      : f a + c + f b + c + f a = a + c + b + c + a)
    : p (f a + c + f b + c + f a + c) = p (a + c + b + c + a + c)
  )
  h_finish
/-
You can notice that
* The expression is build gradually, not in one go.
* We actually run `h_eq a` twice in the proof term, because
  we are rewriting with it on two places, contrary to `rw`.

You might think that the `simp` approach is the more
flexible / general but there are cases where `simp` doesn't work,
and `rw` succeeds. This is due to type dependency issues such as in
the following example.
-/

example (a b : Nat) (h_eq : a = b) (p : ∀ n : Nat, Fin n → Prop)
    (h : ∀ y : Fin b, p b y) : ∀ x : Fin a, p a x := by
  try simp only [h_eq] -- simp cannot do the rewrite
  rw [h_eq] -- rw can, because it rewrites at several places at once
  exact h

/-
# (2) Filling implicit arguments.

When we were applying `congrArg` and `Eq.mpr` in `rw`, we were explicitly filling
the universe levels, and implicit argument. Already there, it was a bit annoying,
and with `simp`, we will need to build much more terms. Fortunatelly, there are
ways to avoid this work.
-/
example (a b c : Nat) (pf1 : a = b) (pf2 : b = c) : True := by
  -- we would like to emulate calling
  have pf3 : a = c := Eq.trans pf1 pf2
  -- but the full expression we want to build is
  have pf3' := @Eq.trans.{1} Nat a b c pf1 pf2
  -- on tactic level, we have several ways to build it
  run_tacq
    -- (a) low-level constructing the term, we have to provide all the arguments
    let lowlev := mkApp6 ((mkConst ``Eq.trans [1])) (mkConst ``Nat) a b c pf1 pf2
    logInfo m!"lowlev = {lowlev}"
    -- (b) using `Qq`
    let pfQ : Q($a = $c) := q(Eq.trans $pf1 $pf2)
    logInfo m!"pfq = {pfQ}"
    -- (c) using `mkAppM`
    let pfAppM ← mkAppM ``Eq.trans #[pf1, pf2]
    logInfo m!"pfAppM = {pfAppM}"
    -- (d) using `mkEqTrans` -- common functions already have their meta-versions
    let pfEqT ← mkEqTrans pf1 pf2
    logInfo m!"pfEqT = {pfEqT}"
  trivial

/-
The crucial difference between `Qq` and `mkAppM` is that `Qq` does the type inference
in compile-time whereas `mkAppM` does it in runtime. Let us implement both as functions.
-/

def buildTransQ {u : Level} {α : Q(Sort u)} {a b c : Q($α)}
    (pf1 : Q($a = $b)) (pf2 : Q($b = $c)) : Q($a = $c) :=
  q(Eq.trans $pf1 $pf2)

def buildTransM (pf1 pf2 : Expr) : MetaM Expr :=
  mkAppM ``Eq.trans #[pf1, pf2]

/-
Notice that `buildTransM` needs to run in MetaM -- only that way it will have enough
data to correctly infer the types of the given expressions, and hence the correct
implicit arguments.

On the other hand, `buildTransQ` doesn't need MetaM. It needs to get all the data
that makes `pf1` and `pf2` correctly annotated: `u α a b c`.
Even if these arguments are passed implicitly (so the meta-programmer doesn't
have to write them), they are indeed passed, and play a crucial role in runtime
to build the resulting term.

We will use `mkAppM` to finish the implementation of `simp`.
Using `Qq` requires taking care of the annotations which can become
a bit finicky (doable but perhaps not as well suited for a tutorial).
On the other hand, we encourage you to try building terms with `Qq` too,
and see what suits your needs better.
-/

/-
## Exercise

Define a function `myCalculation` which takes two numbers
`a b : Nat / Int / Rat`, and builds `a + b * a`
automatically infering their type, and the appropriate typeclass
instance. Try:
* specific functions, you can find them ;-)
* `mkAppM`
* `Qq`

Tip: when editing the middle of the file, it might help to prevent
Lean to from recompiling the rest of the file by typing `#exit`
at the end of the section.
Just don't forget to delete it when you move on ;-).

Hint for Qq: Qq can infer the instance too but you cannot (!!)
pass it implicitly as `[Q(HAdd $α $α $α)]`.
So first, try to pass `Q(HAdd $α $α $α)` as an explicit argument,
and insert `q(inferInstance)` to the call (analogously multiplication).
Later, you can do a trick with a default argument filled with
an `exact` tactic -- you need to fill it with a tactic to postpone
the type inference.
-/

def myCalculation (a b : Expr) : MetaM Expr := do
  return a

-- preliminary, you will have to change the type signature to some `Q(...)`
def myCalcQ2 (a : Expr) (b : Expr) : Expr := a

example (a b : Nat) (c d : Int) (e f : Rat) : True := by
  run_tacq
    let ab ← myCalculation a b
    -- let ab := myCalcQ a b
    let cd ← myCalculation c d
    -- let cd := myCalcQ c d
    let ef ← myCalculation e f
    -- let ef := myCalcQ e f
    logInfo m!"ab := {ab}, cd := {cd}, ef := {ef}"
    unless ← isDefEq ab q($a + $b*$a) do throwError "ab := {ab} != a+b*a"
    unless ← isDefEq cd q($c + $d*$c) do throwError "cd := {cd} != c+d*c"
    unless ← isDefEq ef q($e + $f*$e) do throwError "ef := {ef} != e+f*e"
  trivial

/-
# (3) SimpResult

First, we define a structure capturing the result.

The output of a simplification run on `a` is a new expression `expr`
of the same type, and a proof `pf : a = expr`. Sometimes, `simp` doesn't
perform any simplification, in that case, we allow `pf` to be `none`
(although we could also close it using `rfl`)
-/
structure SimpResult where
  expr : Expr
  pf? : Option Expr

-- Note that the library Simp also has very similar Result structure, both
-- in basic library, and with Qq hints.
#check Simp.Result
#check Simp.ResultQ

/-
Let's prepare some ways to combine results together. There are not too much
iteresting ideas, going on so you can skip to the next section.
-/

def SimpResult.empty (e : Expr) : SimpResult := {expr := e, pf? := none}

#check Eq.refl
/-- (tutorial function)
Gets the proof, possibly building `rfl` if it was none. -/
def SimpResult.getProof (r : SimpResult) : MetaM Expr :=
  match r.pf? with
  | some pf => pure pf
  | none => mkAppM ``Eq.refl #[r.expr]
-- see also `mkEqRefl`

#check Eq.trans
/-- (tutorial function)
Combines two `SimpResults` using `Eq.trans` -/
def SimpResult.trans (r1 r2 : SimpResult) : MetaM SimpResult := do
  match r1.pf? with
  | none => return r2
  | some pf1 => match r2.pf? with
    | none => return {expr := r2.expr, pf? := some pf1}
    | some pf2 =>
      let pf ← mkAppM ``Eq.trans #[pf1, pf2]
      return {expr := r2.expr, pf? := some pf}

#check congr
#check congrArg
#check congrFun
/-- (tutorial function)
Combines `f = g`, and `a = b` into `f a = g b` using `congr` -/
def SimpResult.app (rf rArg : SimpResult) : MetaM SimpResult := do
  let expr := mkApp rf.expr rArg.expr
  match rf.pf? with
  | none => match rArg.pf? with
    | none => return .empty expr
    | some pfArg => return {expr := expr, pf? := ← mkAppM ``congrArg #[rf.expr, pfArg]}
  | some pff => match rArg.pf? with
    | none => return {expr := expr, pf? := ← mkAppM ``congrFun #[pff, rArg.expr]}
    | some pfArg => return {expr := expr, pf? := ← mkAppM ``congr #[pff, pfArg]}
-- see also `mkCongr`, `mkCongrArg`, `mkCongrFun`

/-
# (4) Basic implementation

We split the simplification algorithm into two functions.

* Function `simProcBasic (...) a` only tries to make a single rewrite step
  of the root of `a` to `b` and build a proof of `a = b`.
* Recursive function `simpRec0` gets a specific root-rewriting function as
  an argument (currently `simProcBasic`), tries to apply it anywhere inside
  the term, and returns the proof of equality in the same format.
-/

/-- (tutorial function)
Root-rewriting function analogous to `simp only`.
It gets a list of equalities `rules`, and tries to find a matching
rule `rule : a = b` that matches the given expression `a`.
The `rule` also can be quantified.
On the other hand, we do not look to subexpressions of `a`,
and only try to perform the step once. (that is the job of `simpRec`)
-/
def simProcBasic (rules : List Expr) (a : Expr) :
    MetaM SimpResult :=
  withNewMCtxDepth do
    for rule in rules do
      let eq ← whnf (← inferType rule)
      let (mvars, _, eq) ← forallMetaTelescope eq -- turn quantifiers into mvars
      -- let pf := mkAppN eq mvars -- build the proof term
      let some (_, ar, br) := eq.app3? ``Eq | throwError "Not an equality: {rule} : {eq}"
      if ← withTransparency .reducible (isDefEq a ar) then
        let br ← instantiateMVars br
        let pf := mkAppN rule (← mvars.mapM instantiateMVars)
        return {expr := br, pf? := some pf}
    return .empty a

-- Test!
example (a b : Nat) (f : Nat → Nat) (h : ∀ x, f x = x) : True := by
  run_tacq
    let e := q($f ($a + $b))
    let res ← simProcBasic [h] e
    logInfo m!"Simplify ({e}) to: {res.expr}"
    logInfo m!"Proof term: {res.pf?}"
  trivial

/-- (tutorial function)
Recursive rewrite inside a term.
-/
partial -- simplification could repeat indefinitely, `partial` skips termination check
def simpRec0 (simProc : Expr →  MetaM SimpResult)
  (a : Expr) : MetaM SimpResult := do
  let an ← whnfR a
  let res ← match an with -- try to simplify the inside of the expression
  | .app f arg =>
    let rf ← simpRec0 simProc f
    let rArg ← simpRec0 simProc arg
    rf.app rArg
  | _ => pure <| .empty an
  let resProc ← simProc res.expr -- This is the step actually doing the rewrite!
  if resProc.pf?.isNone then
    return res
  -- if rewrite was successful, we repeat in case there is more to do
  let res ← res.trans resProc
  let resRepeat ← simpRec0 simProc res.expr
  res.trans resRepeat

-- Test rewriting inside the term.
example (a b : Nat) (f : Nat → Nat) (h : ∀ x, f x = x)
  (h_test : 2 * f a = f b * 3): True := by
  run_tacq
    let res ← simpRec0 (simProcBasic [h]) h_test.ty
    logInfo m!"Simplify ({h_test.ty}) to: {res.expr}"
    logInfo m!"Proof term: {res.pf?}"
  trivial

/-
## Using `simp` infrastructure

The library `simp` is similarly modular as ours, with a few extra features. Often,
we don't have to implement the entire `simpRec` from scratch. Let us show how
to perform the same simplification using our own `simProcBasic`
but library's `simp` instead of our own `simpRec`. Notice that
`simp` can simplify inside a binder.
-/

#print Simp.Simproc
#check Simp.main
#check applySimpResultToTarget

example (a b c : Nat) (p : Nat → Nat → Prop)
    (h₁ : a = b) (h₂ : b = c) (finish : ∀ x, p x c → p x c) :
    (∀ x, p x a → p x a) := by
  -- simp only [h₁, h₂]
  run_tacq goal =>
    let ctx : Simp.Context ← Simp.mkContext -- optionally lemmas & extra congruence lemmas
    let method : Simp.Simproc := fun e : Expr => do
      let res ← simProcBasic [h₁, h₂] e
      -- Very straightforward translation from our `SimpResult` to the library
      -- `Simp.Step`. In general, `Simp.Step` can guard the repetition inside
      -- `simp` by deciding on `done` / `visit` / `continue`
      if res.pf?.isNone then return Simp.Step.continue
      else return Simp.Step.visit { expr := res.expr, proof? := res.pf? }
    let methods : Simp.Methods := { pre := method }
    let (res, _stats) ← Simp.main goal.ty ctx (methods := methods)
    logInfo m!"Simplify ({goal.ty}) to: {res.expr}"
    logInfo m!"Proof term: {res.proof?}"
    -- we could match on `res.proof?` but we can also use library function
    let mvarIdNew ← applySimpResultToTarget goal.mvarId! goal.ty res
    if mvarIdNew == goal.mvarId! then throwError "simp made no progress"
    replaceMainGoal [mvarIdNew]
  exact finish

/-
# (5) Debugging with traces

For basic debug prints, we can use `logInfo`, however:
* we have to delete it when we want to hide the debug,
* it can get messy when we print too many messages.

Lean offers a system of traces for debugging purposes. We can
display traces for many standard Lean functions. For example,
`whnf` sometimes calls `trace[trace.Meta.whnf]`, so let us look
at the debug prints.
-/
run_meta
  let e1 : Q(Nat) := q(let x := 3; x^2)
  -- setting the option manually, otherwise we would get much more
  -- traces
  let e2 ← withOptions (fun opt => opt.setBool `trace.Meta.whnf true) do
    whnf e1
  logInfo m!"logInfo e2: {e2}"

-- We can also do this ourself
run_meta
  withOptions (fun opt => opt.setBool `trace.WhateverName true) do
    trace[WhateverName] m!"Hello trace"

/-
But usually, we want to turn the trace on using `set_option`.
Such option must be defined in another imported file. Here,
we registered `MyTrace` in `TutorialAux/Init.Lean`. You get
get to the definition by ctrl-clicking on `trace.MyTrace`
in `set_option`.
-/
set_option trace.MyTrace true in -- try to comment out this line
run_meta
  trace[MyTrace] m!"Hello trace"

-- as with any other option, we can also set the option globally with
set_option trace.MyTrace true
-- or unset
set_option trace.MyTrace false

/-
## Tree Structure

The traces can be packed into a tree with
-/
#check withTraceNode
#check withTraceNode'
#check withTraceNodeBefore

-- for example
set_option trace.MyTrace true in
run_meta
  trace[MyTrace] "Start"
  let res? : Option Nat ← withTraceNodeBefore `MyTrace (pure "Pack 1") do
    trace[MyTrace] "Start inside"
    let a : Nat ← withTraceNode' `MyTrace do
      trace[MyTrace] "Double inside"
      pure (40, m!"obtaining 40")
    trace[MyTrace] "Subresult {a}"
    pure (some a) -- also try one of the following lines instead
    -- return none
    -- throwError "Crashed"
  trace[MyTrace] "Result is {res?}"

/-
Notice that `withTraceNodeBefore` calculates the packed message
at the beginning but the emoticon at the end. This emoticon depends
on the calculated value, which is why we need `Option` or `Bool`
as a return type. Alternatively, we can define `ExceptToEmoji` on
a custom data type.
-/

instance simpResultToEmoji : ExceptToEmoji Exception SimpResult where
  toEmoji x := exceptOptionEmoji (x.map SimpResult.pf?)

set_option trace.MyTrace true in
run_meta
  let res : SimpResult ← withTraceNodeBefore `MyTrace (pure "Pack") do
    let expr := q(2)
    let pf : Q(1 + 1 = 2) := q(rfl)
    trace[MyTrace] "expr := {expr}"
    trace[MyTrace] "pf := {pf}"
    pure ⟨expr, some pf⟩
    -- pure ⟨expr, none⟩
    -- throwError "oops"

/-- (tutorial function) Trace SimpResult if nonempty -/
def SimpResult.trace (res : SimpResult) : MetaM Unit := do
  match res.pf? with
  | some pf =>
    trace[MyTrace] "=> {res.expr}"
    withTraceNode' `MyTrace do
      trace[MyTrace] pf
      pure ((), "(proof term)")
  | _ => pure ()

/-
# (6) Implementing simp inside binders

Here, we look how to implement `simp` inside binders on our own without using
library's `Simp.main`. Let's look again how library's simp does it.
-/
theorem simp_example2 (a b c : Nat) (p : Nat → Nat → Prop)
    (h₁ : a = b) (h₂ : b = c) (finish : ∀ x, p x c → p x c) :
    (∀ x, p x a → p x a) := by
  simp only [h₁, h₂]
  exact finish

#print simp_example2

-- The proof term uses special theorems digging into forall & implication:
#check implies_congr
#check forall_congr

-- Let's start with using these lemmas to build `SimpResult`

#check implies_congr
/-- (tutorial function)
from `a = b`, `c = d` proves `a → c = b → d` using `implies_congr` on `SimpResult`s -/
def SimpResult.impl (r1 r2 : SimpResult) : MetaM SimpResult := do
  let expr := mkForall Name.anonymous BinderInfo.default r1.expr r2.expr
  if r1.pf?.isNone && r2.pf?.isNone then return .empty expr
  return {expr := expr, pf? := some <|
    ← mkAppM ``implies_congr #[← r1.getProof, ← r2.getProof]
  }
-- see also `mkImpCongr`

#check forall_congr
/-- (tutorial function)
Gets a proof of `p fv = q fv` where `fv` is a free variable, and `p fv` is a `Prop`.
and builds a proof of `(∀ x, p x) = (∀ x, q x)` using forall_congr.
-/
def SimpResult.forall (fv : Expr) (r : SimpResult) :
    MetaM SimpResult := do
  let expr ← mkForallFVars #[fv] r.expr -- bind `fv` into forall `expr := ∀ x, q x`
  match r.pf? with
  | none => return .empty expr
  | some pf =>
    let pf ← mkLambdaFVars #[fv] pf -- bind `fv` into lambda, `pf : ∀ x, p x = q x`
    let pf ← mkAppM ``forall_congr #[pf] -- `pf : (∀ x, p x) = (∀ x, q x)`
    return {expr := expr, pf? := some pf}
-- see also `mkForallCongr`

-- Now, we need to update `simpRec0` to use them.

/-- (tutorial function)
Recursive simplification inside a term with implications.
-/
partial
def simpRec (simProc : Expr →  MetaM SimpResult)
  (a : Expr) : MetaM SimpResult := do
  trace[MyTrace] "Simplifying {a}"
  let an ← whnfR a
  let res ← -- try to simplify the inside of the expression
    withTraceNodeBefore `MyTrace (pure "inside") do
    match an with
    | .app f arg =>
      let rf ← simpRec simProc f
      let rArg ← simpRec simProc arg
      rf.app rArg
    | .forallE _name t body _bi =>
      if !body.hasLooseBVars then -- not a dependent implication -> impl_congr
        let rt ← simpRec simProc t
        let rBody ← simpRec simProc body
        rt.impl rBody
      else -- dependent implication -> forall_congr
        if !(← isProp an) then -- forall_congr only works on a Prop
          pure <| .empty an
        else
          -- In general, `forallTelescope` unpacks forall a bit like `intros` creating
          -- new free variables and putting them into the local context within
          -- the inner do scope. Here we want just a single step, hence
          -- `forallBoundedTelescope` with `maxFVars? := some 1`
          forallBoundedTelescope an (some 1) (fun fvars body => do
            -- this `body` has a fvar, contrary to the bare `body`
            -- we got by unpacking the `Expr` which uses a `bvar`
            let res ← simpRec simProc body
            res.forall fvars[0]!
        )
    | _ => pure <| .empty an
  res.trace
  let resProc ←
    withTraceNodeBefore `MyTrace (pure "root") do
    simProc res.expr -- This is the step actually doing the rewrite!
  resProc.trace
  if resProc.pf?.isNone then
    return res
  -- if rewrite was successful, we repeat in case there is more to do
  let res ← res.trans resProc
  let resRepeat ← simpRec simProc res.expr
  res.trans resRepeat

/--
(tutorial function) Simplifies the goal with a `simProc`
-/
def mySimpGoal (simProc : Expr → MetaM SimpResult) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let res ←
      withTraceNodeBefore `MyTrace (pure "Build simp equation") do
      simpRec simProc target -- run simplification
    match res.pf? with
    | none => throwError "mySimpGoal made no progress"
    | some pf =>
      trace[MyTrace] target
      res.trace
      -- use Eq.mpr as with `rw`, this time using `mkAppM`
      let m ← mkFreshExprSyntheticOpaqueMVar res.expr
      goal.assign <| ← mkAppM ``Eq.mpr #[pf, m]
      replaceMainGoal [m.mvarId!]

-- Test!
set_option trace.MyTrace true in
example (a b c : Nat) (p : Nat → Nat → Prop)
    (h₁ : a = b) (h₂ : b = c) (finish : ∀ x, p x c → p x c) :
    (∀ x, p x a → p x a) := by
  -- simp only [h₁, h₂]
  run_tacq mySimpGoal (simProcBasic [h₁, h₂])
  exact finish

/-
Exercise: The implementation above works with ∀ but not with ∃.
Update the function `simpRec` so that the following proof passes.
-/
set_option trace.MyTrace true in
example (a b : Nat) (p : Nat → Nat → Prop)
    (h : a = b) (finish : ∃ x, p x b) :
    (∃ x, p x a) := by
  -- simp only [h]
  run_tacq mySimpGoal (simProcBasic [h])
  exact finish


/-
# (7) Collecting tagged lemmas

The standard `simp` doesn't need to be given the lemmas each usage, it uses
all the lemmas tagged with `@[simp]`. Let us show an example to introduce
a custom attribute `my_tag`.

This requires two `initialize` steps.
* Creating an environment extension `myExt` using
  `registerSimpleScopedEnvExtension`. This will store the array of tagged theorems.
* Registering the attribute `my_tag` itself using `registerBuiltinAttribute`.

Little annoyingly, every `initialize` must be done in another file than
where it is tested (i.e. where we tag theorems with the attribute).

Look at the file `TutorialAux/Tag.lean` where these two steps are done.
-/
#check myExt

-- Since we imported `TutorialAux/Tag.lean`, we can tag some theorems with `my_tag`

@[my_tag] theorem add_assoc_rev (a b c : Nat) :
  a + (b + c) = (a + b) + c := (Nat.add_assoc a b c).symm
@[my_tag] theorem two_mul_rev (a : Nat) : a + a = 2 * a := a.two_mul.symm
-- even some theorems are defined without `@[my_tag]`
theorem two_mul_rev' (a b : Nat) : (b + a) + a = b + 2 * a := by omega
theorem two_two_four (a : Nat) : 2 * (2 * a) = 4 * a := by omega
-- we can add the attribute later
attribute [my_tag] two_mul_rev'
attribute [my_tag] two_two_four

-- look at the theorems stored at `customExt`
run_meta
  let state := myExt.getState (← getEnv)
  for (e,t) in state do
    logInfo m!"{e} : {t}"

/-
Now, we have all the ingredients to an alternative to `simProcBasic`.
This will use tagged theorems (tagged when the is run), and allow
quantified theorems.
-/
#check simProcBasic
def simProcTag (expr : Expr) : MetaM SimpResult :=
  withNewMCtxDepth do
    let state := myExt.getState (← getEnv)
    for (e,t) in state do
      let (mvars, _, eq) ← forallMetaTelescope t -- turn quantifiers into mvars
      let pf := mkAppN e mvars -- build the proof term
      let some (_, ar, br) := eq.app3? ``Eq | throwError "Not an equality: {pf} : {eq}"
      if ← withTransparency .reducible (isDefEq expr ar) then
        let br ← instantiateMVars br
        let pf ← instantiateMVars pf
        return {expr := br, pf? := some pf}
    return .empty expr

set_option trace.MyTrace true in
example (a : Nat) (p : Nat → Prop) (h : p (4*a + 2*a + a)) :
    p ( (a+a+a)+a+(a+a+a) ) := by
  run_tac mySimpGoal simProcTag
  exact h

/-
Exercise: Update the code for `Tag.lean` & `simProcTag` so that
it can accept theorems with universe levels.
-/

#check eq_self
attribute [my_tag] eq_self

example (a : Nat) : a + a = 2 * a := by
  run_tac mySimpGoal simProcTag
  exact True.intro

-- Hints:
#check getConstInfo
#check mkFreshLevelMVarsFor
-- Feel free to change the type (Expr × Expr) stored in `myTag`
-- the pair `(e,t)` might not be ideal. Also remember that the metavariables
-- must be introduced when trying to apply a theorem, not at initialization
-- because we want different mvar instantiations at different places.
