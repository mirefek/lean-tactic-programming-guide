import Batteries
import Lean
import Qq

/-!
# Tutorial: Writing `rw` from scratch

Content
(1) What `rw` does on proof term level?
(2) Basic implementation
(3) Options for normalization
(4) Unification - rewriting a quantified equality
-/

open Lean Elab Meta Tactic
open Qq

/-
# (1) What rw does on proof term level, and what is the difference?

Let as look at an example proof using `rw`.
-/

theorem rw_example (a b : Nat) (f : Nat → Nat) (p : Nat → Prop)
    (h_eq  : ∀ x : Nat, f x = x) (h_finish : p (a + b + a + b)) :
    p (f a + f b + f a + f b) := by
  rw [h_eq] -- rewrites two instances of `f a`
  rw [h_eq] -- rewrites two instances of `f b`
  exact h_finish

-- and print its proof term
#print rw_example

-- it should look similar to
example : ∀ (a b : Nat) (f : Nat → Nat) (p : Nat → Prop),
  (∀ (x : Nat), f x = x) → p (a + b + a + b) → p (f a + f b + f a + f b) :=
fun a b f p h_eq h_finish =>
  Eq.mpr (
    congrArg (fun X => p (X + f b + X + f b)) (h_eq a : f a = a)
    : p (f a + f b + f a + f b) = p (a + f b + a + f b)
  )
  (Eq.mpr (
    congrArg (fun X => p (a + X + a + X)) (h_eq b : f b = b)
    : p (a + f b + a + f b) = p (a + b + a + b)
  ) h_finish)

-- You can see two main theorems used for each rewrite:
#check congrArg -- digging into a subterm
#check Eq.mpr -- translate equality to implication

/-
Because of the theorems that `rw` is using, it first instantiates
the hypothesis `h_eq`, and then replaces all the instances in the goal
by a single call of `congrArg`.
-/

/-
(intermezzo) the role of `id`
You can also see some `id` in the proof which is the identity function.
It is used for typing -- `id` can change a type of its value in case
they are definitionally equal.
On metaprogramming level, this appeared in the proof by using
-/
#check mkExpectedPropHint

/-
# (2) Implementing `rw`.

## Abstracting a variable

In the basic version, we will be only rewriting a term
with a single equality without quantifiers.

Say we are rewriting `A = B` in some expression
`e := ... A ... A ...`
First, we want to locate all the `a`-s in the expression,
and build a mapping
`fun X => ... X ... X ...`

This is called an abstraction, first we need to locate all `A`s in `e`,
and replace them with a corresponding `bvar`. A `bvar` is a variable
pointing to a quantifier with an index where quantifiers are indexed
from the inner-most to the outer-most.
To determine which `bvar` index to use, we carry `offset`.
-/
/-- (tutorial function) simplified `kabstract` -/
def myAbstract (e a : Expr) (offset : Nat := 0) : MetaM Expr := do
  if !e.hasLooseBVars then  -- we cannot rewrite a subterm containing a variable bound in `e`
    if (← isDefEq e a) then  -- check if already `a` is already the root
      return mkBVar offset  -- replace with bvar
  -- otherwise, we recurse
  match e with -- ctrl-click on `e.update...` to see the definition
  | .app f x         => return e.updateApp! (← myAbstract f a offset) (← myAbstract x a offset)
  | .mdata _ b       => return e.updateMData! (← myAbstract b a offset) -- `b` = body
  | .proj _ _ b      => return e.updateProj! (← myAbstract b a offset)
  | .letE _ t v b _  =>
    return e.updateLetE! (← myAbstract t a offset) -- diving under a binder -> increase offset
      (← myAbstract v a offset) (← myAbstract b a (offset+1))
  | .lam _ d b _     => return e.updateLambdaE! (← myAbstract d a offset) (← myAbstract b a (offset+1))
  | .forallE _ d b _ => return e.updateForallE! (← myAbstract d a offset) (← myAbstract b a (offset+1))
  | e                => return e

-- lean's implementation is slightly more advanced but still readable
#check kabstract

-- the difference is that `kabstract` allows choosing positions,
-- where to apply the rewrite
def myAbstractAt (pos : Nat) (e a : Expr) :=
  kabstract e a (.pos [pos])

-- Let's see
example (a b : Nat) (h : (2 * a + b + 1) = (2 * b + a + 1)) : True := by
  run_tacq
    let e1 ← myAbstract h.ty a
    let e2 ← kabstract h.ty a
    -- kabstract does the same as myAbstract
    -- the #0 represents a bvar which is not bounded in the printed term
    logInfo m!"e1: {e1}\ne2: {e2}"
    -- Let's see how we can choose the positions for `kabstract`.
    logInfo m!"pos1: {← myAbstractAt 1 h.ty a}"
    logInfo m!"pos2: {← myAbstractAt 2 h.ty a}"
    -- exercise: Re-implement `myAbstractAt` from scratch,
    -- without using `kabstract`. Can you understand how
    -- `kabstract` uses a State monad to do it?
  trivial

-- Now, we can build the mapping
/-- (tutorial function) Runs `kabstract`, and wraps the result to a lambda. -/
def abstractToMapping (e a : Expr) : MetaM Expr := do
  -- make sure that all previous mvar assignments were applied in `e`
  -- this is necessary to recurse the term, not for `isDefEq`, so `a` doesn't need it
  let e ← instantiateMVars e
  let body ← myAbstract e a  -- replace `a` with a `bvar`
  return mkLambda
    `X -- name for the variable, due to `bvar`s, we don't have to care about collisions,
    BinderInfo.default -- could be also e.g. `implicit` (braces instead of parentheses)
    (← inferType a) -- type for the variable
    body

-- Let's building the lambda
example (A : Nat) (h : -- some crazy expression containing various constructions
    ∀ (y : Nat), (y = A) →
    let z := A + y
    y + A = (fun (X : Nat) => X + A - y) z -- no worry about the same name
  ) : True := by
  -- `run_tacq` is like `run_tac` but makes the context directly accessible
  -- not useful for writing tactics but handy for testing
  run_tacq
    logInfo m!"Before: {h.ty}" -- Qq-type (compile-time)
    let f ← abstractToMapping h.ty A
    logInfo m!"After: {f}"
  trivial

/-
## Decomposing equality
-/
/-- (tutorial function)
`decomposeEq` takes a proof of equality `pf : a = b`, where `(a b : α : Sort u)`,
and returns (u, α, a b)
-/
def decomposeEq (pf : Expr) : MetaM (Level × Expr × Expr × Expr) := do
  let t ← inferType pf
  -- `whnf` helps to get `Eq` at the root, removing mdata,
  -- instantiating mvars, expanding definitions...
  let t ← whnf t
  match t with
  | .app (.app (.app (.const ``Eq [u]) α) a) b =>
    return (u, α, a, b)
  | _ => throwError "given term {pf} : {t} is not a proof of equality"

-- we also could have used `Expr.app3? ``Eq`, or
-- `matchEq?` but that doesn't give us the level
#check Expr.app3?

/-
## Building proof term
-/

/--
(tutorial function)
Takes a term `t := ... A ...`, and an equation
`eq : A = B`, and returns a proof of `... B ... → ... A ...`.
-/
def proveRwImp (eq t : Expr) :
  MetaM Expr := do
  let (u, α, a, b) ← decomposeEq eq
  -- find the abstract function
  let f ← abstractToMapping t a
  logInfo m!"lhs := {a}, rhs := {b}\nabstr := {f}"
  -- we also detect the sort level of t (usually Prop)
  let tt ← inferType t
  let v := (← inferType tt).sortLevel!
  let rw_eq := mkApp6 -- build `@congrArg.{u,v} α tt a b f eq : f a = f b`
    (mkConst ``congrArg [u,v])
    α tt a b f eq
  logInfo m!"rw_eq := {rw_eq}"
  -- We know `f a = t` (definitionally)
  -- Now let's calculate `f b` using famous "beta reduction".
  let fb := f.beta #[b]
  -- semantically it is the same as f.app b but the goal is not as pretty ;-)
  -- try to uncomment the following line to see the difference:
  -- let fb := f.app b
  if !tt.isSort then -- why `t` must be a sort to build an implication?
    throwError m!"Cannot convert equality between {tt} to an implication"
  -- finally, let's build the implication
  return mkApp3 -- build `Eq.mpr.{v-1} (f a) (f b) rw_eq`
    (mkConst ``Eq.mpr [tt.sortLevel!])
    t fb rw_eq

#check congrArg
#check Eq.mpr

/-
Let's test the function `proveRwImp`, and finish
the goal rewrite inside `run_tacq` script
-/
example (a b : Nat) (h : a = b) : 2*a + b = 2*b + a := by
  run_tacq goal =>
    let t := q($a + 5 - $a)
    -- try what happens with a non-prop term by uncommenting the next line
    let imp ← proveRwImp h goal.ty
    let imp_t ← inferType imp
    -- test the result of `proveRwImp`
    logInfo m!"imp : {imp_t}"
    -- finish rewriting the goal
    let mt := imp_t.bindingDomain!
    logInfo m!"Build mvar of type {mt}"
    let m ← mkFreshExprSyntheticOpaqueMVar mt
    goal.mvarId!.assign (mkApp imp m)
    replaceMainGoal [m.mvarId!]
  -- check that we have successfully rewritten the main goal
  rfl

/-
# (3) Options for normalization

There are two places where normalization happens in the code of `rw` above.
* Calling `whnf` in decomposing equality
* The `isDefEq` check to determine whether to perform the abstraction.

Full normalization is not always desired, let us see an example of what can happen.
-/
def myAdd (a b : Nat) : Nat := a + b
def myEq (a b : Nat) : Prop := (a = b)

example (a b c : Nat) (h : myEq (myAdd a b) (myAdd b c))
    (h2 : a + b = c) : True := by
  run_tacq
    let htn ← whnf h.ty
    logInfo m!"{h.ty}\n→ {htn}" -- whnf unpacks `myEq`
    let (u,α,lhs,rhs) ← decomposeEq h
    logInfo m!"lhs := {lhs}, rhs := {rhs}" -- so `decomposeEq` splits the equality
    -- This is a nice feature :-)

    -- similarly isDefEq unpacks the definition
    logInfo m!"({h.ty}) ?= ({htn}) : {← isDefEq h.ty htn}"
    -- so myAbstract catches such occurence too
    logInfo m!"Abstracting ({lhs}) in ({h2.ty}):\n{← abstractToMapping h2.ty lhs}"
    -- This is rather confusing, we see no `(myAdd a b)` in `a + b = c`.
  trivial

-- In both cases, normalization is performed based on the Meta.Config
#check Meta.Config
/-
To see all the options, Ctrl-click on that type to see all the options with their
explanation. There are many options to look at such as `beta`, `zeta`, `zetaDelta`.
For example, to prevent `1 + 3` being identified with 4, we need
`offsetCnstrs := false`

Here, we focus on the example of transparency -- expanding definitions.
-/
#check Meta.Config.transparency
-- The most typical options are
#check TransparencyMode.default
#check TransparencyMode.reducible -- prevent the above definition expansion

/-
Let us see how to set reducible transparency. The config lives
in a Reader monad, meaning it is read-only. We cannot change the config
for the outside code but we can run a local piece of code with a changed config.
-/
#check withConfig
#check withTransparency

example (a b : Nat) (h1 : a = b) (h2 : myEq a b) : True := by
  run_tacq
    logInfo m!"isDefEq default: {← isDefEq h1.ty h2.ty}"
    -- general context-changing scope
    withConfig (fun cfg => {cfg with transparency := .reducible}) do
      -- anything running here ras reducible trnasparency
      logInfo m!"isDefEq reducible1: {← isDefEq h1.ty h2.ty}"
    -- setting transparency in particular has a shortcut
    withTransparency .reducible do
      logInfo m!"isDefEq reducible2: {← isDefEq h1.ty h2.ty}"
    -- we should do this when matching `lhs` to an expression

    -- the same works with whnf
    logInfo m!"whnf default: {← whnf h2.ty}"
    withTransparency .reducible do
      logInfo m!"whnf reducible1: {← whnf h2.ty}"
    -- `whnfR` is a shortcut for above
    logInfo m!"whnf reducible2: {← whnfR h2.ty}"
  trivial

/-
# (6) Unification - rewriting a quantified equality.

Now, we want to be able to rewrite quantified equality, for example we have a rule
`∀ a b : Nat, p a + b = a + q b`,
and we want to use it to rewrite `p 1 + 2` to `1 + q 2`.
The main idea is to first replace the quantified variables with metavariables to obtain
`p ?a + ?b = p ?b + ?a`
Now the left hand side is structurally the same as `p 1 + 2` up to the
metavariables, so we need to find the right value for them.

## Unification

Finding values for metavariables actually happens automatically:
-/
example (p : Nat → Nat) : True := by
  run_tacq
    let a ← mkFreshExprMVarQ q(Nat) (userName := `a) -- just a Qq-sugar on top
    let b ← mkFreshExprMVarQ q(Nat) (userName := `b) -- of `mkFreshExprMVar`
    let pattern := q($p $a + $b)
    let rhs := q($a + $p $b)
    let target := q($p 1 + 2)
    logInfo m!"matching {target} with {pattern}\n→ {rhs}" -- not assigned
    if ← isDefEq pattern target then -- The magic happens here!
      logInfo m!"matched {target} with {pattern}\n→ {rhs}" -- assigned
    else
      logInfo "Couldn't match"
    logInfo m!"If match succeesed, the mvars are now assigned: a = {a}, b = {b}"
    -- Note that using MessageData is crucial - the expressions `a`, `b` didn't change,
    -- only the way we look at them inside MetaM Monad.
    logInfo s!"As a string, we still see the metavariables:\na = {a}, b = {b}"
    let a2 ← instantiateMVars a
    let b2 ← instantiateMVars b
    logInfo s!"Unless we instantiate:\na2 = {a2}, b2 = {b2}"
  trivial

/-
As we saw, `isDefEq` is not just an innocent check, it can modify the proofstate
by assiging metavariables.
Besides checking modulo basic reductions, it tries to find variable assignment that
satisfies the equality. If there exist an assignment, the asignment is performed in
the proofstate, and `isDefEq` return `true`. On the other hand, if the return value
is `false`, we know there was no change in the proof state.

## Controling assignable meta-variables

There are two factors deciding whether a metavariable can be automatically
assigned with `isDefEq`. We have already seen the meta-variable kind.
-/
run_meta
  let mNat1 ← mkFreshExprMVarQ q(Nat) .natural `mNat1
  let mNat2 ← mkFreshExprMVarQ q(Nat) .natural `mNat2
  let mSyn1 ← mkFreshExprMVarQ q(Nat) .synthetic `mSyn1
  let mSyn2 ← mkFreshExprMVarQ q(Nat) .synthetic `mSyn2
  -- natural mvars prefer to be assigned over synthetic
  logInfo m!"mNat1 = mSyn1: {← isDefEq mNat1 mSyn1}"
  logInfo m!"mSyn2 = mNat2: {← isDefEq mSyn1 mNat1}"
  logInfo m!"{mNat1} = {mSyn1}, {mNat2} = {mSyn2}"
  -- but synthetic can be assigned too if needed
  logInfo m!"mSyn1 = mSyn2: {← isDefEq mSyn1 mSyn2}"
  logInfo m!"{mSyn1} = {mSyn2}"
  -- contrary to synthetic opaque
  let mSO1 ← mkFreshExprMVarQ q(Nat) .synthetic `mSO1
  let mSO2 ← mkFreshExprMVarQ q(Nat) .synthetic `mSO2
  logInfo m!"mSO1 = mSO2: {← isDefEq mSO1 mSO2}"

/-
Often, we also want to prevent previously created mvars to be assigned no matter
of their kind. This can be done by entering a new `MetavarContext.depth`.
-/
#check withNewMCtxDepth
run_meta
  let mNat1 ← mkFreshExprMVarQ q(Nat) .natural `mNat1
  let mNat2 ← mkFreshExprMVarQ q(Nat) .natural `mNat2
  -- normally, mNat would be prefered to be assigned,
  -- we block it by entering a new level
  withNewMCtxDepth do
    logInfo m!"mNat1 = mNat2: {← isDefEq mNat1 mNat2}" -- now, they cannot be assigned
    let mSyn ← mkFreshExprMVarQ q(Nat) .synthetic `mSyn
    -- but a new synthetic can be assigned to them
    logInfo m!"mSyn = mNat1: {← isDefEq mSyn mNat1}"
    logInfo m!"{mSyn} = {mNat1}"
/-

## Quantified `rw`

Since we used `isDefEq` in `myAbstract`, it should be no surprise now why
rewriting with a quantified equality matches its first instantiation.
The unification happens the first moment it can, and later `f a` cannot
get unified with `f b`.

Let us finish the implementation by turning quantifiers into metavariables.
The function to do it is `forallMetaTelescope`
-/
#check forallMetaTelescope
-- rewrite a quantified equality
example (a b : Nat) (f : Nat → Nat) (p : Nat → Prop)
    (h_eq  : ∀ x : Nat, f x = x) (h_finish : p (a + b + a + b)) :
    p (f a + f b + f a + f b) := by
  run_tacq goal =>
    let imp ← withNewMCtxDepth do
      let (mvars, _, eq) ← forallMetaTelescope h_eq.ty -- turn quantifiers into mvars
      let pf_eq := mkAppN h_eq mvars -- build the proof term
      logInfo m!"before: {pf_eq} : {eq}"
      -- the same rewrite code as before
      let imp ← withTransparency .reducible <| proveRwImp pf_eq goal.ty
      logInfo m!"after: {pf_eq} : {eq}"
      -- we need to instantiate the variables before exiting the MCtx context
      instantiateMVars imp
    let imp_t ← inferType imp
    logInfo m!"imp_t2 := {imp_t}"
    let mt := imp_t.bindingDomain!
    let m ← mkFreshExprSyntheticOpaqueMVar mt
    goal.mvarId!.assign (mkApp imp m)
    replaceMainGoal [m.mvarId!]
  -- successfully rewritten `f a` → `a`
  rw [h_eq b] -- let's do the second step with a simple `rw` :-)
  trivial

-- Exercise: Implement the full `my_rw` tactic
example (a b : Nat) (f : Nat → Nat) (p : Nat → Prop)
    (h_eq  : ∀ x : Nat, f x = x) (h_finish : p (a + b + a + b)) :
    p (f a + f b + f a + f b) := by
  my_rw h_eq
  my_rw h_eq
  exact h_finish
