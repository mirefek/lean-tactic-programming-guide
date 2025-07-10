import Batteries
import Lean
import Qq
import TutorialAux.Tag -- for Section (6)

/-!
This file explains and implements basic versions of `rw` & `simp` tactics.
-/

open Lean Elab Meta Tactic
open Qq

/-
# Writing rw / simp from scratch

Content
(1) What `simp` & `rw` do on proof term level, and what is the difference?
(2) Implementing `rw`
(3) Options for normalization
(4) Filling implicit arguments
(5) Implementing `simp`
(6) Unification - rewriting a quantified equality
(7) Collecting tagged lemmas
-/

/-
# (1) What simp & rw do on proof term level, and what is the difference?

You probably know that the main difference between `simp only` and `rw` is
that `simp only` rewrites as long as it can, while `rw` rewrites just once.

The background reason is a fundamental differences between the terms
proof produced.

## What `rw` does
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
In proofs, it is used for typing -- `id` can change a type of its value
in case they are definitionally equal.

Consider `weirdNat` defined with a obfuscated type
definitionally equal to `Nat`.
-/
def weirdNat : (fun t _ => t) Nat 8 := 4
#check weirdNat
-- just an annotation will not change the type
#check (weirdNat : Nat)
-- but using id could
#check @id Nat weirdNat

-- On metaprogramming level, this appeared in the proof by using
#check mkExpectedPropHint

/-
## What `simp` does

Simp doesn't do all its equal rewrites in one go.
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
This is muc hmore messy but after prettification, you could get the following proof term.
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
-/

/-
You might think that the `simp` approach is the more
flexible / general but there are cases where `simp` doesn't work,
and `rw` succeeds. This is due to type dependency issues as in
the following example.
-/

example (a b : Nat) (h_eq : a = b) (p : ∀ n : Nat, Fin n → Prop)
    (h : ∀ y : Fin b, p b y) : ∀ x : Fin a, p a x := by
  -- simp only [h_eq] -- simp cannot do the rewrite
  rw [h_eq] -- rw can, because it rewrites at several places at once
  exact h

/-
Sure, in more basic cases, simp is able to rewrite
inside binders because it uses special rules for that.
Let's look at the following proof.
-/
theorem simp_example2 (a b : Nat) (p : Nat → Nat → Prop)
    (h : a = b) (finish : ∀ x, p x b → p x b) : (∀ x, p x a → p x a) := by
  simp only [h]
  exact finish

-- If we print the proof term
#print simp_example2
-- we can see two special rules used
#check implies_congr
#check forall_congr

/-
# (2) Implementing `rw`.

## Abstracting a variable

In the basic version, we will be only rewriting a term
with a single equality without quantifiers.

Say we are rewriting `A = B` in some expression
`e := ... A ... A ...`
First, we want to locate all the `a`-s in the expression,
and build a mapping
`fun x => ... x ... x ...`

This is called an abstraction, first we need to locate all `A`s in `e`,
and replace them with a corresponding `bvar`.
A `bvar` is a variable pointing to a quantifier with an index
where quantifiers are indexed from the inner-most to the outer-most.
To know the index for the `bvar`, we carry `offset`.
-/
/-- (tutorial function) simplified `kabstract` -/
def myAbstract (e a : Expr) (offset : Nat := 0) : MetaM Expr := do
  if !e.hasLooseBVars then  -- we cannot rewrite a subterm containing a variable bound in `e`
    if (← isDefEq e a) then  -- check if already `a` is already the root
      return mkBVar offset  -- same as `Expr.bvar offset`
  -- otherwise, we recurse
  match e with
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

-- Now, we can build the mapping
/-- (tutorial function) Runs `kabstract`, and wraps the result to a lambda. -/
def abstractToMapping (e a : Expr) : MetaM Expr := do
  -- make sure that all previous mvar assignments were applied in `e`
  -- this is necessary to recurse the term, not for `isDefEq`, so `a` doesn't need it
  let e ← instantiateMVars e
  let body ← myAbstract e a  -- replace `a` with a `bvar`
  return mkLambda
    `x -- name for the variable, due to `bvar`s, we don't have to care about collisions,
    BinderInfo.default -- could be also e.g. `implicit` (braces instead of parentheses)
    (← inferType a) -- type for the variable
    body

-- Let's test
example (A : Nat) (h : -- some crazy expression containing various constructions
    ∀ (y : Nat), (y = A) →
    let z := A + y
    y + A = (fun (x : Nat) => x + A - y) z -- no worry about the same name
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

-- we also could have used `Expr.app3? ``Eq` but that doesn't give us the level
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
For example:
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
    -- similarly isDefEq unpacks the definition
    logInfo m!"({h.ty}) ?= ({htn}) : {← isDefEq h.ty htn}"
    -- so myAbstract catches such occurence too
    logInfo m!"Abstracting ({a}) in ({h2.ty}):\n{← abstractToMapping h2.ty a}"
  trivial

-- In both cases, normalization is performed based on the Meta.Config
#check Meta.Config
/-
To see all the options, Ctrl-click on that type to see all the options with their
explanation. There are many options to look at such as `beta`, `zeta`, `zetaDelta`...

Here, we focus on the example of transparency -- expanding definitions.
-/
#check Meta.Config.transparency
-- The most typical options are
#check TransparencyMode.default
#check TransparencyMode.reducible -- prevent the above definition expansion

/-
Let us show some ways to set reducible transparency. The config lives
in so-called Reader monad, meaning it is read-only. We cannot change
the config for the outside code but we can run a local piece of code
with a changed config.
-/
#check withConfig
#check withTransparency

example (a b : Nat) (h1 : a = b) (h2 : myEq a b) : True := by
  run_tacq
    logInfo m!"isDefEq default: {← isDefEq h1.ty h2.ty}"
    -- general context-changing scope
    withConfig (fun cfg => {cfg with transparency := .reducible}) do
      logInfo m!"isDefEq reducible1: {← isDefEq h1.ty h2.ty}"
    -- setting transparency in particular
    withTransparency .reducible do
      logInfo m!"isDefEq reducible1: {← isDefEq h1.ty h2.ty}"
    -- the same works with whnf
    logInfo m!"whnf default: {← whnf h2.ty}"
    withTransparency .reducible do
      logInfo m!"whnf reducible1: {← whnf h2.ty}"
    -- `whnfR` is a shortcut for above
    logInfo m!"whnf reducible2: {← whnfR h2.ty}"
  trivial

/-
# (4) Filling implicit arguments.

When we were applying `congrArg` and `Eq.mpr`, we were explicitly filling
the universe levels, and implicit argument. Already there, it was a bit annoying,
and with `simp`, we will need to build much more terms. Fortunatelly, there are
ways to avoid this work.
-/
example (a b c : Nat) (pf1 : a = b) (pf2 : b = c) : True := by
  -- we would like to emulate calling something like
  have pf3 : a = c := Eq.trans pf1 pf2
  -- but the full expression we want to build is
  have pf3' := @Eq.trans.{1} Nat a b c pf1 pf2
  -- on tactic level, we have several ways to construct it
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
# (5) Implementing `simp`

## SimpResult

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

-- let's prepare some ways to combine results together

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

/-
## Main functions `SimpRec` & `SimpBase`

Later, we will also want to simplify tagged quantified equations,
so we split the simplification algorithm into two functions.

* Function `simpBase (...) a` only tries to make a single rewrite step
  of the root of `a` to `b` and build a proof of `a = b`. This function will
  later get an upgrade.
* Recursive function `simpRec` gets a specific root-rewriting function as
  an argument (currently `simpBase`), and tries to apply it anywhere inside
  the term, and returns the proof of equality in the same format.
-/

/-- (tutorial function)
Simple root-rewriting function.
It gets a list of equalities `rules`, and tries to find a rule
`rule : e = b` that exactly matches the given expression `e`.
It doesn't dig inside `e`, and only tries to perform the step once.
-/
def simpBase (rules : List Expr) (a : Expr) :
    MetaM SimpResult := do
  for rule in rules do
    let eq ← whnf (← inferType rule)
    let some (_, ar, br) := eq.app3? ``Eq | throwError "Not an equality: {rule} : {eq}"
    if ← isDefEq a ar then
      return {expr := br, pf? := some rule}
  return .empty a

/-- (tutorial function)
Recursive rewrite inside a term.
-/
partial -- simplification could repeat indefinitely, `partial` skips termination check
def simpRec (base : Expr →  MetaM SimpResult)
  (a : Expr) : MetaM SimpResult := do
  let an ← whnfR a
  let res ← match an with -- try to simplify the inside of the expression
  | .app f arg =>
    let rf ← simpRec base f
    let rArg ← simpRec base arg
    rf.app rArg
  | .forallE _name t body _bi =>
    if !body.hasLooseBVars then -- not a dependent implication -> impl_congr
      let rt ← simpRec base t
      let rBody ← simpRec base body
      rt.impl rBody
    else -- dependent implication -> forall_congr
      if !(← isProp an) then -- forall_congr only works on a Prop
        pure <| .empty an
      else
        -- In general, `forallTelescope` unpacks forall a bit like `intros` creating
        -- new free variables and putting them into the local context within
        -- the inner do scope. Here we want just a single step, hence
        -- `forallBoundedTelescope` with `some 1`
        forallBoundedTelescope an (some 1) (fun fvars body => do
          -- this `body` has a fvar, contrary to the bare `body`
          -- we got by unpacking the `Expr` which uses a `bvar`
          let res ← simpRec base body
          res.forall fvars[0]!
      )
  | _ => pure <| .empty an
  let resBase ← base res.expr -- This is the step actually doing the rewrite!
  if resBase.pf?.isNone then
    return res
  -- if rewrite was successful, we repeat in case there is more to do
  let res ← res.trans resBase
  let resRepeat ← simpRec base res.expr
  res.trans resRepeat

/--
(tutorial function)
-/
def mySimpGoal (base : Expr → MetaM SimpResult) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let res ← simpRec base target
    logInfo m!"Simplified to {res.expr}"
    match res.pf? with
    | none => throwError "mySimpGoal made no progress"
    | some pf =>
      logInfo m!"proof of equality: {pf}"
      -- use Eq.mpr as before, this time using `mkAppM`
      let m ← mkFreshExprSyntheticOpaqueMVar res.expr
      goal.assign <| ← mkAppM ``Eq.mpr #[pf, m]
      replaceMainGoal [m.mvarId!]

-- Test!
example (a b c : Nat) (p : Nat → Nat → Prop)
    (h₁ : a = b) (h₂ : b = c) (finish : ∀ x, p x c → p x c) :
    (∀ x, p x a → p x a) := by
  -- simp only [h₁, h₂]
  run_tacq mySimpGoal (simpBase [h₁, h₂])
  exact finish

/-
## Using `simp` infrastructure with a `simproc`

The library `simp` is similarly modular as ours, with a few extra features. Often,
we don't have to implement the entire `simpRec` from scratch. Let us show how
to perform the same simplification using our own `simpBase` but library's `simp`.
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
      let res ← simpBase [h₁, h₂] e
      -- Very straightforward translation from our `SimpResult` to the library
      -- `Simp.Step`. In general, `Simp.Step` can guard the repetition inside
      -- `simp` by deciding on `done` / `visit` / `continue`
      if res.pf?.isNone then return Simp.Step.continue
      else return Simp.Step.visit { expr := res.expr, proof? := res.pf? }
    let methods : Simp.Methods := { pre := method }
    let (res, _stats) ← Simp.main goal.ty ctx (methods := methods)
    logInfo m!"Simplified to {res.expr}"
    -- we could match on `res.proof?` as above but we can also use library function
    let mvarIdNew ← applySimpResultToTarget goal.mvarId! goal.ty res
    if mvarIdNew == goal.mvarId! then throwError "simp made no progress"
    replaceMainGoal [mvarIdNew]
  exact finish

/-
# (6) Unification - rewriting a quantified equality.

Now, we want to be able to rewrite quantified equality, say we have the rule
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
    logInfo m!"matching {target} with {pattern} → {rhs}" -- not assigned
    if ← isDefEq pattern target then -- The magic happens here!
      logInfo m!"matched {target} with {pattern} → {rhs}" -- assigned
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
In fact, `isDefEq` is not just an innocent check, it can modify the proofstate
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
Often, we want to prevent existing mvars to be assigned. This can be done
by entering a new `MetavarContext.depth`.
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
In rewriting, we want to only assign the currently build variables,
so we use this feature.

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
      -- we need to instantiate the variables before exiting the Mctx context
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

/-
Since we imported this `Tutorial/Tag.lean`, we can now tag some theorems with `my_tag`
-/

#check Nat.add_assoc

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
Now, we have all the ingredients to an alternative to `simpBase`.
This will use tagged theorems (tagged when the is run), and allow
quantified theorems.
-/
#check simpBase
def simpWithTagged (expr : Expr) : MetaM SimpResult := do
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

example (a : Nat) (p : Nat → Prop) (h : p (4*a + 2*a + a)) :
    p ( (a+a+a)+a+(a+a+a) ) := by
  run_tac mySimpGoal simpWithTagged
  exact h

/-
Exercise: Update the code for `Tag.lean` & `simpWithTagged` so that
it can accept theorems with universe levels.
-/

#check eq_self
attribute [my_tag] eq_self

example (a : Nat) : a + a = 2 * a := by
  run_tac mySimpGoal simpWithTagged
  exact True.intro

-- Hints:
#check getConstInfo
#check mkFreshLevelMVarsFor
-- Feel free to change the type (Expr × Expr) stored in `myTag`
-- the pair `(e,t)` might not be ideal. Also remember that the metavariables
-- must be introduced when trying to apply a theorem, not at initialization
-- because we want different mvar instantiations at different places.
