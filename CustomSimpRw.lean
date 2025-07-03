import Batteries
import Lean
import Qq

open Lean Elab Meta Tactic
open Qq

/-
# Writing rw / simp from scratch

Content
(1) What simp & rw do on proof term level, and what is the difference?
(2) Implementing `rw` using bare expressions.
(3) Implementing `simp` using Qq.
(4) Unification - rewriting a quantified equality.
(5) Collecting tagged lemmas
(6) Simplification procedures - building upon existing simp infrastructure

Leave for another file
* Options for `whnf`
* Options for unification
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
updated, it directly uses
-/
#check congr

theorem simp_example (a b c : Nat) (f : Nat → Nat) (p : Nat → Prop)
    (h_eq  : ∀ x : Nat, f x = x) (h_finish : p (a + c + b + c + a + c)) :
    p (f a + c + f b + c + f a + c) := by
  simp only [h_eq]
  exact h_finish

#print simp_example

/-
After prettification, you could get the following proof term.
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
It is not as clean as with `rw`, but you can notice that
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
# (2) Implementing `rw` using bare expressions.

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

-- lean implements this with a slightly more advanced but still readable
#check kabstract

-- Now, we can build the mapping
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
/--
`decomposeEq` takes a proof of equality `pf : a = b`, where `(a b : α : Sort u)`,
and returns (u, α, a b)
-/
def decomposeEq (pf : Expr) : MetaM (Level × Expr × Expr × Expr) := do
  let t ← inferType pf
  let t ← whnf t -- helps to get `Eq` at the root, removing mdata, instantiating mvars...
  match t with
  | .app (.app (.app (.const ``Eq [u]) α) a) b =>
    return (u, α, a, b)
  | _ => throwError "given term {pf} : {t} is not a proof of equality"

-- we also could have used `Expr.app3? ``Eq` but that doesn't give us the level
#check Expr.app3?

/-
## Building proof term

Now, we write a function that takes an equation
a term `t := ... A ...`, and an equation `eq : A = B`,
and returns a proof of `... B ... → ... A ...`.
-/
def proveRwImp (eq t : Expr) :
  MetaM Expr := do
  let (u, α, a, b) ← decomposeEq eq
  -- find the abstract function
  let f ← abstractToMapping t a
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
# (3) Implement `simp` using Qq

For simp, we will utilize Qq to both showcase it, and to get some type safety.
For start, we will not expect `simp` to automatically search for / apply theorems,
we only provide it a finite list of fixed equalities it can use.

We are not aiming at efficiency. Contrary to the standard `simp`
which skips proving reflexivity, we will prove reflexivity at the atomic terms,
and will propagate it upwards (just for for coding convenience).

First, we define a structure capturing the result.
-/
/--
The output of a simplification run on `a` of type `α : Sort u`
is a proof `pf : a = b`. We need to store all of its typing
information also to be able to specify its Qq-type.
-/
structure SimpResult {u : Level} {α : Q(Sort u)} (a : Q($α)) where
  b : Q($α)
  pf : Q($a = $b)

-- Note that the library Simp also has a similar Result structure, both
-- in basic library, and with Qq hints, we will not use that for now
#check Simp.Result
#check Simp.ResultQ

/-
Now, we prepare infrastructure for composing `SimpResult`s together.
-/

#check rfl
/-- Builds a result for no rewrite -/
def SimpResult.rfl {u : Level} {α : Q(Sort u)} (a : Q($α)) : SimpResult a := ⟨a, q(rfl)⟩

def SimpResult.isRfl {u : Level} {α : Q(Sort u)} {a : Q($α)} (r : SimpResult a) :=
  r.pf.isAppOfArity ``rfl 2

#check Eq.trans
/-- runs `Eq.trans` on `SimpResult`s -/
def SimpResult.trans {u : Level} {α : Q(Sort u)} {a : Q($α)}
    (r1 : SimpResult a) (r2 : SimpResult r1.b) : SimpResult a :=
  let ⟨_,pf1⟩ := r1
  let ⟨b2,pf2⟩ := r2
  ⟨b2, q(Eq.trans $pf1 $pf2)⟩

-- TODO: explain filling implicit variables
-- TODO: tell about mkAppM

-- TODO: explain there is a lot of work behind writing this

#check congr
/-- runs `congr` on `SimpResult`s -/
def SimpResult.app {u v : Level} {α : Q(Sort u)} {β : Q(Sort v)}
    {af : Q($α → $β)} {aArg : Q($α)}
    (rf : @SimpResult _ q($α → $β) af) (rArg : SimpResult aArg) :
    SimpResult q($af $aArg) :=
  let ⟨bf, pff⟩ := rf
  let ⟨bArg, pfArg⟩ := rArg
  ⟨q($bf $bArg), q(@congr $α $β $af $bf $aArg $bArg $pff $pfArg)⟩

#check implies_congr
/-- runs `implies_congr` on `SimpResult`s -/
def SimpResult.impl {u v : Level} {a1 : Q(Sort u)} {a2 : Q(Sort v)}
    (r1 : @SimpResult _ q(Sort u) a1) (r2 : @SimpResult _ q(Sort v) a2) :
    SimpResult (q($a1 → $a2)) :=
  let ⟨b1, pf1⟩ := r1
  let ⟨b2, pf2⟩ := r2
  ⟨q($b1 → $b2), q(implies_congr $pf1 $pf2)⟩

-- TODO: Notice we are sometimes in bare Expr

#print forall_congr
#check forall_congr
def SimpResult.forall {u : Level} {α : Q(Sort u)}
    (p q : Q($α → Prop)) (fv : Q($α)) (h : Q($p $fv = $q $fv))
    (name : Name) (bi : BinderInfo) :
    Q((∀ x, $p x) = (∀ x, $q x)) :=
  have h : Q(∀ x, $p x = $q x) :=
    mkLambda name bi α (h.abstract #[fv])
  let res : Q((∀ x, $p x) = (∀ x, $q x)) :=
    q(forall_congr $h)
  -- we don't want to see the explicit applications `p a`, `p b`,
  -- so we use `mkExpectedPropHint` to change the output type
  -- to something definitionally equal.
  have lhs : Q(Prop) := mkForall name bi α p.bindingBody!
  have rhs : Q(Prop) := mkForall name bi α q.bindingBody!
  mkExpectedPropHint res q($lhs = $rhs)

/-
TODO: explain better simpRec & simpBase

To make it modular, we have
* function `simpBase (...) a` that only tries to make a single rewrite step
  of the root of `a` to `b` and build a proof of `a = b`. If the root doesn't,
  simpllify, it just leaves `b` as `a`, and closes the proof with reflexivity.
* recursive function `simpRec` which gets a specific
  root-rewriting function as an argument, tries to apply
  it anywhere inside the term, and returns the proof of equality in the same format.
-/

/--
This is the main simple root-rewriting function.
It gets a list of equalities `rules`, and tries to find a rule
`rule : e = b` that exactly matches the given expression `e`.
It doesn't dig inside `e`, and only tries to perform the step once.
-/
def simpBase (rules : List Expr) (u : Level) (α : Q(Sort u)) (a : Q($α)) :
    MetaM (SimpResult a) := do
  -- unfortunatelly, Qq-matching is not a friend with imperative constructions
  -- such as `for .. do`, so we use a monadic alternative `List.findSomeM?`
  let result? : Option (@SimpResult u α a)
    ← rules.findSomeM? fun rule =>
      have rule : Q(Prop) := rule
      match rule with
      | ~q($a = $b) =>
        return (some ⟨b, rule⟩)
      | _ => return none
  return match result? with
  | some result => result
  | none => SimpResult.rfl a

partial -- simplification could repeat indefinitely, `partial` skips termination check
def simpRec (base : (u : Level) → (α : Q(Sort u)) → (a : Q($α)) →  MetaM (SimpResult a))
  {u : Level} {α : Q(Sort u)} (a : Q($α)) : MetaM (SimpResult a) := do
  -- Qq-matching doesn't work for highly abstract terms
  -- TODO: whnf & match on
  -- (f a)
  -- (a → b)
  -- ∀ x, p x
  throwError "not finished"
  -- TODO: simplify children
  -- let prev : SimpResult := none.
  -- match base e with
  -- | none => prev
  -- | some res =>

/-
# (4) Unification - rewriting a quantified equality.
-/

-- TODO:
-- basics of unification theory (first-order in almost linear time,
--   second order undecidable, but lean has some heuristics)
-- in practice
-- * replace forall with metavariables
-- * explain & run isDefEq

/-
# (5) Collecting tagged lemmas
-/

-- TODO: look into it, understand, explain

theorem cancel_around (x : Nat) : 1 + x - 1 = x := sorry

attribute [simp] cancel_around
-- TODO: look at gcongr example in mathlib
#check registerSimpleScopedEnvExtension


/-- Environment extension for "generalized congruence" (`gcongr`) lemmas. -/
abbrev GCongrLemma := Nat

initialize gcongrExt : SimpleScopedEnvExtension ((Name × Name × Array Bool) × GCongrLemma)
    (Std.HashMap (Name × Name × Array Bool) (Array GCongrLemma)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, lem) => m.insert n ((m.getD n #[]).push lem)
    initial := {}
  }

-- TODO

/-
# (6) Simplification procedures - building upon existing simp infrastructure
-/
