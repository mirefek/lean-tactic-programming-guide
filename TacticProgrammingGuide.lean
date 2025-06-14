import Lean -- Lean's metaprogramming
import Batteries
import Qq -- convenient term building / matching

/-
This tutorial is intended for people who have basic knowledge of
Lean theorem prover, as well as some basic programming,
and would be interested to know how to implement a custom tactic in Lean.

Ideally open this file in VSCode to see how Lean reacts.

After going through this tutorial, you should have a decent overview
of what Lean metaprogramming is about, and be able to write some
simple tactics.

# Beginner's Guide to Lean Tactic Programming

Tactics are in principle arbitrary programs that opearate on the proof state.
We can write such programs in place in the tactic proof, such as in
the following example.

This example tactic doesn't do anything except logging "Hello world".
Put your cursor at the blue-underlined run_tac to see the message.

Do not bother by the type of Lean.logInfo too much so far,
it is simply a logging / printing function.
-/

example : True := by
  run_tac
    Lean.logInfo "Hello world!"
  trivial

/-
To understand how to write tactics, we need to understand
(1) How imperative programs work in Lean
(2) What really is a proof state
(3) What are the basic data structures around Lean metaprogramming
(4) Some API to modify the proof state
(5) How to declare syntax for a new tactic

Let us answer them.

## (1) How imperative programs work in Lean

Lean is a pure functional language -- compared to
imperative languages (C, Python, ...),
its definitions cannot change, and its functions depend only on the arguments,
and cannot have side effects.

However, functional programming languages (such as Haskell) developed
a way to write imperative style through
* theory of monads
* do syntax to hide most of monads from the user.

We will keep the monad theory hidden, here we just say that a monad
in general denotes an imperative program. There are several monads depending
on what state they have access to. In the following example, we show an example
of two monads.

Lean.Elab.Tactic.TacticM -- the top level tactic monad, has access to
  all the data from the proofstate
Lean.Meta.MetaM -- a monad that only has access to information about
  metavariables (not important for now). This is a part of the entire
  proofstate, so a TacticM can call a MetaM but not the other way around
  (we would have to provide the TacticM all the extra data it needs)

We simply demostrate imperative programming in Lean is
by showing an example. We are still not using any API to access
the proofstate (except logInfo), only showcasing Lean as an imperative
programming language.
-/

namespace Chapter1Coding

-- a MetaM monad returning a Nat
-- the "do" is important to use "do notation", otherwise, we would have to
-- use Lean's standard syntax, and compose the monad manually

--         parameters     monad type   return value
--             v               v         v
def myCode1 (n : Nat) : Lean.Meta.MetaM Nat := do
  if n = 0 then -- since we are in a do notation, we can skip "else"
    return 42
  let k := n^2 -- we use ":=" to assign a value
  Lean.logInfo m!"{n} -> {k}"
  return k

-- a TacticM monad taking a Nat, without a return value
-- here the "do" is actually not necessary, since it is a single command
def myCode2 (n : Nat) : Lean.Elab.Tactic.TacticM Unit := do
  Lean.logInfo m!"Calling Tactic1 ({n})"

-- a TacticM monad returning an array of Nat,
-- Array is basically the same thing as List with a different
-- implementation (analogous to C++ vectors)
def myCode3 : Lean.Elab.Tactic.TacticM (Array Nat) := do
  Lean.logInfo "Calling Tactic2"
  myCode2 7
   -- lean variables are immutable but the do notation
   -- allows to break this
  let mut a := #[] -- "#" denotes it is an empty Array instead of empty List
  for i in List.range 5 do
    let res ← myCode1 i -- we use "←" to retrieve a value from a monad execution
    a := a.push res -- an assignment without "let" only allowed for mutable variables
    -- Note: since we immediatelly replace a with (a.push i),
    --   Lean's inner optimization will avoid duplicating the array
    -- Note for imperative programmers:
    --   "a.push res" alone cannot work, an external function cannot
    --   change the value of "a", Lean is a pure functional language
    --   after all
    (Lean.logInfo m!"got: {res}" : Lean.Elab.Tactic.TacticM Unit)
    -- Note: The type annotation is not necessary. It just helps Lean compiler
    -- to be faster. Try to delete it to see what happens.
  myCode2 15
  return a

/-
Look at what Lean prints, and see if you can understand where all the messages
come from.
-/
example : True := by
  run_tac
    Lean.logInfo "Running some tactic programs 2!"
    let x ← myCode3
    -- Notice that it is possible to inline monad evaluation
    -- inside an expression, using (← someTactic)
    Lean.logInfo m!"result: {x} %% {← myCode1 5}"
  trivial

end Chapter1Coding

/-
Of course, this is not exhaustive, advanced topics include
* What is the theory behind monads, how to use custom monads.
* What are further programming-focused functions & datastructures in Lean,
  such as Std.HashMap, foldM, etc
* different types of exceptions -- panic, throwError
...

## (2) What really is a proof state

On the core level, a proof is a term, so called "proof term" that
testifies the truth of the given proposition.
When we are proving a theorem, at every moment, we have a partially
built proof term with holes, so called metavariables.
Once all metavariables are assigned, the proof is finished.
Syntactically, metavariables start with a questionmark.

As an example, we show a proof of "p → p ∧ True", and write
the partially filled proof term in between.
-/

namespace Chapter2Datatypes

theorem p_imp_p_true (p : Prop) : p → p ∧ True := by
  -- example : True ∧ True := ?_
  intro h
  -- example : True ∧ True := (fun h => ?_)
  constructor
  -- example : True ∧ True := (fun h => And.intro ?left ?right)
  assumption
  -- example : True ∧ True := (fun h => And.intro h ?right)
  trivial
  -- example : True ∧ True := (fun h => And.intro h True.intro)

end Chapter2Datatypes

/-
## (3) What are the basic data structures around Lean metaprogramming

* Expressions -- Lean.Expr, Qq
* data in expressions: Lean.Name, Lean.MVarId, Lean.FVarId
* printing: String, Format, MessageData
-/

namespace Chapter3Datatypes

-- The basic data format is Expression -- ctrl-click
-- on Lean.Expr below to check its definition in the library.
#check Lean.Expr
-- Due to the nature of dependent type theory,
-- expressions are used for terms, propositions, types, and proofs.

-- Lean has a handy library Qq to build Expr with a convenient notation.
open Qq

-- Q(...) is a type annotation of an expression, and
-- q(...) is
def t1 : Q(Prop) := q(True)
def t2 : Q(Prop) := q(∀ p : Prop, p → p ∧ True)

-- Writing expressions directly is possible
-- but can take a bit of effort.
#eval t1
#eval t2

-- The type in Qq is not explicitly Expr but it is definitionally equal to it,
-- and it is not forced to have a correct type. So think of Qq a bit as of
-- Python type annotations -- it can catch basic errors but it is not
-- forced at all.
def t1e : Lean.Expr := t1
def t1x : Q(Nat) := t1

#check t1e
#check t1x

-- Basically all Lean types are in namespace Lean,
-- repeating the prefix is getting annoying
open Lean

-- Further important type used in Lean Metaprogramming is

-- Lean.Name
def n1 : Name := `Nat.blah -- single backtick = arbitrary name
def n2 : Name := ``t1e -- double backtick = resolve name

#print n1
#print n2

-- The way Expr handles variables might seem messy at first -- there are
#check Expr.bvar -- variable bound / quantified inside that Expr, represented with an index
#check Expr.fvar -- variable in the context
#check Expr.mvar -- metavariable
#check Expr.const -- a defined constant

-- Moreover, the username is never a unique identifier of a variable,
-- Lean wants to allow in principle multiple variables with the same name.
-- so free variables are identified by
#check FVarId
#check MVarId
-- these datatypes hide a name inside too but that name (such as _uniq.13541)
-- should never be ever exposed to the user.

/-
Showing / printing.
Our basic printing function logInfo is a bit trickier, in normal
programming languages, we are used to a print function that takes a
String. However, in Lean, logInfo can show a term that allows
mouse hover showing types, etc. In fact, there is
-/
#check MessageData -- interactive expression
#check Format -- almost string (with) pretty-printing metadata)
#check String -- standard list of characters

-- Examine the print of the following logInfo.
example : True := by
  run_tac
    logInfo m!"Interactive MessageData: {t2}"
    logInfo s!"String: {t2}"
  trivial

end Chapter3Datatypes

/-
## (4) Basic API to modify the proof state

Let us write the code for the 4 tactics used in
-/
#check Chapter2Datatypes.p_imp_p_true
example (p : Prop) : p → p ∧ True := by
  intro h; constructor; assumption; trivial

namespace Chapter4TacticCode

/-
A lot of the functions / types are hidden in namespaces
* Lean
* Lean.Meta
* Lean.Elab.Tactic
so let's open them
-/

open Lean Meta Lean.Elab.Tactic Qq

-- The easiest tactic to replace is "trivial"
def runTrivial0 : TacticM Unit := do
  -- we retrieve the metavariable represesnting the current goal
  let goal : MVarId ← getMainGoal
  -- and assign it to be True.intro
  goal.assign q(True.intro) -- !!! first attempt, not ideal
  -- better to avoid low-level MVarId.assign, we will see why

example (p : Prop) : p → p ∧ True := by
  intro h; constructor; assumption
  run_tac runTrivial0
-- Goals closed :-).

/-
This works nicely but the assignment is unsafe,
it doesn't perform a type check!
Let's try to close also the goal (?left : p) with
runTrivial0 to see what happens.
-/

example (p : Prop) : p → p ∧ True := by -- !!!
  intro h; constructor
  run_tac runTrivial0
  run_tac runTrivial0

/-
MVarId.assign happily closed the goal. Then we correctly
closed the goal (?right : p), and at the very end,
after Lean examined the entire proof term, we got
a mysterious error that we cannot put together
"@And.intro p True" and "True.intro"
because it expects a proof of p.

Such errors are hard to decode, so it is better to ensure
that we only set a mvar when we can.
Fortunatelly, Batteries have
a function that checks if something can be assigned.
-/
#check MVarId.assignIfDefEq

-- correct version
def runTrivial : TacticM Unit := do
  -- we retrieve the metavariable represesnting the current goal
  let goal : MVarId ← getMainGoal
  -- and assign it to be True.intro
  goal.assignIfDefEq q(True.intro)

-- now we got the correct error if we try to run runTrivial2
-- on the wrong goal
example (p : Prop) : p → p ∧ True := by
  intro h; constructor
  run_tac runTrivial -- error where it should be :-)
  run_tac runTrivial

/-
To implement assumption, we want to loop through
all the assumptions, and try to use them.
So we need
* Access to the assumptions
* Exception handling

How do we get the local context? In general contexts are
assigned to metavariables but we can just use
withMainContext.
It stores the context assigned to the current goal
in the monadic state,
and then retrieve the context using getLCtx

First, we can just print the assumptions.
-/

example (n : Nat) (hn : n > 5) : True := by
  run_tac
    -- Note: You will see _example in the list, which is there in case
    -- we wanted to build a recursive definition
    withMainContext do
      let ctx ← getLCtx
      -- go through all local declarations
      -- Note: the questionmark in decl? is just a part of the name
      --   (option type practice)
      for (decl? : Option LocalDecl) in ctx.decls do
        match decl? with
        | some (decl : LocalDecl) =>
          (logInfo m!"{mkFVar decl.fvarId} : {decl.type}  -- {repr decl.kind}" : TacticM Unit)
        | none => pure ()
  trivial

-- We have all the components, so let's implement the assumption tactic.

def runAssumption : TacticM Unit := -- we don't have to start with do here (but can)
  withMainContext do -- but have to do it here
    let goal ← getMainGoal
    let ctx ← getLCtx
    for (decl? : Option LocalDecl) in ctx.decls do
      match decl? with
      | some (decl : LocalDecl) =>
        if decl.kind != .default then continue
        try
          goal.assignIfDefEq (mkFVar decl.fvarId)
          return -- if succeeded, we are done
        catch _ =>
          pure () -- ignore the exception
      | none => pure ()
    throwError "Assumption not found"

-- let's test
example (p : Prop) : p → p ∧ True := by
  intro h; constructor
  run_tac runAssumption
  run_tac runTrivial

/-
The remaining two tactics require creating a new metavariable.
A new metavariable is created using.
-/
#check mkFreshExprMVar
/-
However a good practice is to make the goal variables
"syntheticOpaque" -- then Lean knows that they are somewhat
important, and doesn't unify them willy-nilly.

One way is to use the following function
-/
#check mkFreshExprSyntheticOpaqueMVar
/-
although if you Ctrl-click on it, you find that it just
calls mkFreshExprMVar with a specific kind.
-/

/-
In our runConstructor, we will decompose And.
(we will not attempt general constructor)
First, we just write the function that reads the type A ∧ B from the goal,
and extracts the two type expressions A and B.
-/
def extractAndGoals1 : TacticM (Expr × Expr) := do
  let tgt ← getMainTarget -- equivalent to (← getGoal).getType
  have quotedTgt : Q(Prop) := tgt -- change the apparent type
  match quotedTgt with
  | ~q($p ∧ $q) => -- Qq match, must run in MetaM or higher
    return (p, q)
  | _ => throwError m!"Goal {tgt} is not of the form (?_ ∧ ?_)"

/-
Qq is handy but it is worth knowing how to do these
things "manually"
-/
def extractAndGoals2 : TacticM (Expr × Expr) := do
  let tgt ← getMainTarget
  -- an alternative syntax to match ... with
  let (`And, #[p, q]) := tgt.getAppFnArgs
    | throwError m!"Goal {tgt} is not of the form (?_ ∧ ?_)"
  return (p, q)

-- let's check that our decomposition of "And" works.
example (p q : Prop) (h : p ∧ q) : p ∧ q := by
  run_tac
    let (a1,b1) ← extractAndGoals1
    logInfo m!"Qq extraction: {a1} AND {b1}"
    let (a2,b2) ← extractAndGoals2
    logInfo m!"Expr extraction: {a1} AND {b1}"
  assumption

/--
Replaces the main goal (?_ : A ∧ B) with
And.intro (?left : A) (?right : B)
-/
def runConstructor : TacticM Unit := do
  withMainContext do -- try to comment out this line to see what breaks
    let goal ← getMainGoal
    let ((a : Q(Prop)), (b : Q(Prop))) ← extractAndGoals1
    let left : Q($a) ← mkFreshExprMVar a (userName := `left) -- build new metavariables
    let right : Q($b) ← mkFreshExprMVar b (userName := `right)
    goal.assign q(And.intro $left $right) -- can we be brave here with .assign? :-)
    -- the list of active goals is not maintained automatically,
    -- we need to tell the proof state that we created two new goals
    replaceMainGoal [left.mvarId!, right.mvarId!]

-- let's test
example (p : Prop) : p → p ∧ True := by
  intro h;
  run_tac runConstructor
  run_tac runAssumption
  run_tac runTrivial

def runIntro (name : Name) : TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let lctx ← getLCtx
    let .forallE _ type body c ← goal.getType
      | throwError "Goal not of the form of an implication or quantification"
    let fvarId : FVarId ← mkFreshFVarId -- allocate new variable
    let lctx' := lctx.mkLocalDecl fvarId name type c -- put into a new context
    let fvar : Expr := mkFVar fvarId
    let body := body.instantiate1 fvar -- convert bvar to fvar
    withLCtx' lctx' do
      -- mkFreshExprMVar uses the current monadic context to
      let newMVar ← mkFreshExprMVar body (kind := .syntheticOpaque)
      let newVal ← mkLambdaFVars #[fvar] newMVar
      goal.assign newVal
      replaceMainGoal [newMVar.mvarId!]

-- Note: Since Lean already implemented intro,
-- there is a shortcut ;-)
def runIntro2 (name : Name) : TacticM Unit := do
  let goal ← getMainGoal
  let (_, m) ← goal.intro name
  replaceMainGoal [m]

example (p : Prop) : p → p ∧ True := by
  run_tac runIntro `h
  run_tac runConstructor
  run_tac runAssumption
  run_tac runTrivial

/-
In this example, we did goal-oriented tactics,
so let us show how we could add a new have element
to the local context.
-/
example (a b : Prop) (ha : a) (hab : a → b) : b := by
  run_tac
    withMainContext do
      let goal ← getMainGoal
      let lctx ← getLCtx
      -- find appropriate free variables
      let some ehab := lctx.findFromUserName? `hab | throwError "not found"
      let some eha := lctx.findFromUserName? `ha | throwError "not found"
      let e : Expr := (.app -- build the term "hab ha"
        (mkFVar ehab.fvarId)
        (mkFVar eha.fvarId)
      )
      let t ← inferType e -- t = "b", e = "hab hb"
      -- goal: ctx |- mainGoal
      let goal2 ← goal.assert `hb t e
      -- goal2: ctx |- t -> mainGoal
      let (_, goal3) ← goal2.intro `hb
      -- goal3: ctx, t |- mainGoal
      replaceMainGoal [goal3]
  exact hb

end Chapter4TacticCode

/-
## (5) How to declare syntax for a new tactic

TODO: to be honest, I (Mirek) don't understand this much,
so I am happy to learn here too :-).

I should be able to write
the syntax for the 4 tactics from the previous chapter
(fair start, so can can complete the example),
but then I would like to understand more features of the "elab"
command, and when it must be split into "syntax". Also I think this
is the place to outline what the Syntax type is.
-/

/-
## Finishing notes

There is much more to say,
You can check out a more advanced Lean Metaprogramming book
https://leanprover-community.github.io/lean4-metaprogramming-book/
Another nice resource of what could be a problem when you get stuck
on a mysterious metaprogramming problem:
https://github.com/leanprover-community/mathlib4/wiki/Metaprogramming-gotchas

But also, just be curious -- ctrl-click on the functions we are using
to see what they are doing.

You can also ctrl-click on a monad, such as
TacticM or MetaM (and others you will get into such as TermElabM),
and you will see the extra states it has
(as Context & State), as well as the monad below.
There states can be a bit scary but all the information Lean
has to its disposal must be somewhere in them...
-/
