import Lean -- Lean's metaprogramming
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

However, functional programming languages (such as Haskell) have
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

I think the best way to demostrate imperative programming in Lean is
by showing an example. Except Lean.logInfo, we are still not using any
API to access the proofstate, only showcasing Lean as an imperative
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
    -- Lean's inner optimization will avoid duplicating the array
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
#check Expr.bvar -- variable bound / quantified inside that Expr
#check Expr.fvar -- variable in the context
#check Expr.mvar -- metavariable
#check Expr.const -- a defined constant

#check Meta.Context
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
#check Format -- ignore for now, string with pretty-printing metadata
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
that we only set a mvar when we can. Unfortunatelly,
the safe function is not as intuitive as MVarId.assign.

The right approach is utilize the function "isDefEq".
This is a monadic function that returns a Bool but it does more than
the name suggests. If there are metavariables in the expressions,
isDefEq tries to assign them in order to make the two expressions equal.
If it succeeds, it returns True, and the metavariables remain assigned.
If it returns False, the two terms cannot be made the same,
and nothing changed.

Let's fix the tactic.
-/

-- correct version
def runTrivial : TacticM Unit := do
  -- we retrieve the metavariable represesnting the current goal
  let goal : MVarId ← getMainGoal
  -- and assign it to be True.intro
  unless ←isDefEq (mkMVar goal) q(True.intro) do
    throwError m!"Goal {← goal.getType} is not True"

-- now we got the correct error if we try to run runTrivial2
-- on the wrong goal
example (p : Prop) : p → p ∧ True := by
  intro h; constructor
  run_tac runTrivial -- our error :-)
  run_tac runTrivial

/-
It looks that assumption should be similarly easy.
We would like to go through all assumptions in the current context,
try isDefEq with all of them, and finish if it succeeds.

How do we get the local context? In general contexts are
assigned to metavariables but we can just use
withMainContext.
It stores the context assigned to the current goal
in the monadic state,
and then retrieve the context using getLCtx

First, we can just print the assumptions.
-/

#check MetaM

example (n : Nat) (hn : n > 5) : True := by
  run_tac
    withMainContext do
      let ctx ← getLCtx
      -- go through all local declarations
      -- Note: the questionmark is just a part of the name
      --   (option type practice)
      for (decl? : Option LocalDecl) in ctx.decls do
        match decl? with
        | some (decl : LocalDecl) =>
          (logInfo m!"{mkFVar decl.fvarId} : {decl.type}" : TacticM Unit)
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
        if ←isDefEq (mkMVar goal) (mkFVar decl.fvarId) then
          return -- succeeded :-), we don't need anything else
      | none => pure ()
    throwError "Assumption not found"

-- let's test
example (p : Prop) : p → p ∧ True := by
  intro h; constructor
  run_tac runAssumption
  run_tac runTrivial

/-
The remaining two tactics require creating a new metavariable.
in runConstructor, we just decompose And, contrary to the general tactic.
First, we just write the function that decomposes and And expression
in two ways, using Qq, and using raw terms.
-/

def extractAndGoals1 : TacticM (Expr × Expr) := do
  let tgt ← getMainTarget -- equivalent to (← getGoal).getType
  have quotedTgt : Q(Prop) := tgt -- change the apparent type
  match quotedTgt with
  | ~q($p ∧ $q) => -- Qq match, needs at least MetaM to work
    return (p, q)
  | _ => throwError m!"Goal {tgt} is not of the form (?_ ∧ ?_)"

/-
Qq is handy but is not always reliable, so it is worth knowing
how to do these things "manually"
-/
def extractAndGoals2 : TacticM (Expr × Expr) := do
  let tgt ← getMainTarget
  let tgt ← whnf tgt -- optional, head simplification
  match tgt.getAppFnArgs with
  | (`And, #[p, q]) =>  return (p, q)
  | _ => throwError m!"Goal {tgt} is not of the form (?_ ∧ ?_)"

-- let's check that our decomposition of "And" works.
example (p q : Prop) (h : p ∧ q) : p ∧ q := by
  run_tac
    let (a1,b1) ← extractAndGoals1
    logInfo m!"Qq extraction: {a1} AND {b1}"
    let (a2,b2) ← extractAndGoals2
    logInfo m!"Expr extraction: {a1} AND {b1}"
  assumption

-- Now, let's build the goal
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

-- TODO: implement intro

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
But also, just be curious -- ctrl-click on the functions we are using
to see what they are doing.

You can also ctrl-click on a monad, such as
TacticM or MetaM (and others you will get into such as TermElabM),
and you will see the extra states it has
(as Context & State), as well as the monad below.
There states can be a bit scary but all the information Lean
has to its disposal must be somewhere in them...
-/
