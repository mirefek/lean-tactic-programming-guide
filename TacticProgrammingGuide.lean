import Lean -- Lean's metaprogramming
import Batteries
import Qq -- convenient term building / matching

namespace MetaProgrammingTutorial

/-
This tutorial is intended for people who have basic knowledge of the Lean theorem prover,
as well as some basic programming experience, and would be interested to know how to
implement a custom tactic in Lean.

Ideally open this file in VSCode to see how Lean reacts.

After going through this tutorial, you should have a decent overview of what
Lean metaprogramming is about, and be able to write some simple tactics.

# Beginner's Guide to Lean Tactic Programming

Tactics are in principle arbitrary programs that operate on the proof state.
We can write such programs in-place in the tactic proof, such as in the following example.

This example tactic doesn't do anything except logging "Hello world".
Put your cursor at the blue-underlined `run_tac` to see the message.

Do not bother with the type of `Lean.logInfo` too much so far,
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

Lean is a pure functional language - compared to imperative languages (C, Python, ...),
its definitions cannot change, and its functions depend only on their arguments,
and cannot have side effects.

However, functional programming languages (such as Haskell) developed
a way to write imperative style through
* the theory of monads
* "do notation" to hide most of monads from the user.

We will keep the monad theory hidden, here we just say that a monad in general denotes
an imperative program. There are several monads depending on what state they have access to.
In the following example, we show two monads.

`Lean.Elab.Tactic.TacticM` - the top level tactic monad, has access to all the data
  from the proofstate
`Lean.Meta.MetaM` - a monad that only has access to information about metavariables
  (not important for now). This is a part of the entire proofstate, so a `TacticM`
  can call a `MetaM` but not the other way around (we would have to provide the
  `TacticM` all the extra data it needs)

We will now demonstrate imperative programming in Lean with some examples. So far,
we are not using any API to access the proofstate, only showcasing
Lean as an imperative programming language.
-/

--         parameters     monad type   return value
--             v               v         v
def myCode1 (n : Nat) : Lean.Meta.MetaM Nat := do
  if n = 0 then -- since we are in a do notation, we can skip "else"
    return 42
  let k := n^2 -- we use ":=" to assign a value
  Lean.logInfo m!"{n} -> {k}"
  return k

--         parameters       monad type    no return value (like void in C)
--             v                  v               v
def myCode2 (n : Nat) : Lean.Elab.Tactic.TacticM Unit := do
  Lean.logInfo m!"Calling myCode2 {n}"

-- Array is basically the same thing as List with a different
-- implementation (analogous to C++ vectors)
def myCode3 : Lean.Elab.Tactic.TacticM (Array Nat) := do
  Lean.logInfo "Calling myCode3"
  myCode2 7
   -- lean variables are immutable but the do notation
   -- allows to break this using "let mut"
  let mut a : Array Nat := #[] -- "#" denotes it is an empty Array instead of empty List
  for i in [:5] do -- `[:5]` or `[0:5]` loops through `0,1,2,3,4` using `Std.Range`
    let res ← myCode1 i -- we use "←" to retrieve a value from a monad execution
    a := a.push res -- an assignment without "let" is only allowed for mutable variables
    -- Note: since we immediately replace `a` with `a.push res`,
    --   Lean's inner optimization will avoid duplicating the array
    -- Note for imperative programmers:
    --   `a.push res` alone cannot work, an external function cannot change the value of "a".
    --   Lean is a pure functional language after all
    Lean.logInfo m!"got: {res}"
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
    -- inside an expression, using `← someTactic`
    Lean.logInfo m!"result: {x} %% {← myCode1 5}"
  trivial

/-
Of course, this is not exhaustive. Advanced topics include
* What is the theory behind monads, how to use custom monads.
* What are further programming-focused functions & datastructures in Lean,
  such as `Std.HashMap`, `foldM`, the `IO` monad, etc.
* different types of exceptions -- `throwError`, `panic!`
* `partial` functions to bypass Lean's termination checker
...

## (2) What really is a proof state

On the core level, a proof is a term, a so called "proof term" that testifies the truth
of the given proposition. When we are proving a theorem, at every moment, we have
a partially built proof term with holes, so called metavariables.
Most tactic steps fill one hole (formally assign one metavariable) with a subterm,
possibly containing further metavariables.

The proof is finished once all metavariables are assigned,
i.e. all holes are filled, i.e all goals are closed.
Metavariables are the variables with a question mark before their name.

As an example, we will show a proof of `p → p ∧ True`, and write
the partially filled proof term in between.
-/

theorem p_imp_p_true (p : Prop) : p → p ∧ True := by
  -- p_imp_p_true : p → p ∧ True := ?_
  intro h
  -- p_imp_p_true : p → p ∧ True := (fun h => ?_)
  constructor
  -- p_imp_p_true : p → p ∧ True := (fun h => And.intro ?left ?right)
  assumption
  -- p_imp_p_true : p → p ∧ True := (fun h => And.intro h ?right)
  trivial
  -- p_imp_p_true : p → p ∧ True := (fun h => And.intro h True.intro)

/-
## (3) What are the basic data structures around Lean metaprogramming

* Expressions - `Lean.Expr`, `Qq`
* data in expressions: `Lean.Name`, `Lean.MVarId`, `Lean.FVarId`
* printing: `String`, `Format`, `MessageData`
-/

-- The data structure that is used to represent Lean expressions is `Lean.Expr`.
-- Due to the nature of dependent type theory, `Lean.Expr` is used to encode types, terms and proofs.
-- Thus, `Lean.Expr` is also what is checked by the Lean kernel when checking proofs.
-- ctrl-click on `Lean.Expr` below to see its definition in the library.
#check Lean.Expr

-- Lean has a handy library `Qq` to help you build `Lean.Expr` terms with a convenient notation.
open Qq

-- `Q(...)` is a type annotation of an expression, and
-- `q(...)` is an expression
def t1 : Q(Prop) := q(True)
def t2 : Q(Prop) := q(∀ p : Prop, p → p ∧ True)

-- Writing expressions directly is possible
-- but can take a bit of effort.
#eval t1
#eval t2

-- The type `Q(...)` is not explicitly `Lean.Expr` but it is definitionally equal to it,
-- and it is not forced to have a correct type annotation. So you can think of Qq
-- as of Python type annotations - it can catch basic errors but it is not forced at all.
def t1e : Lean.Expr := t1
def t1x : Q(Nat) := t1

#check t1e
#check t1x

-- Basically all metaprogramming API is in the namespace `Lean`
-- repeating the prefix is getting annoying
open Lean

-- Another important type in metaprogramming is `Lean.Name`
def n1 : Name := `Nat.blah -- single backtick: arbitrary name
def n2 : Name := ``t1e -- double backtick: resolved name (resolved in the current context)

#print n1
#print n2

-- The way Expr handles variables might seem messy at first - there are
#check Expr.bvar -- variable bound / quantified inside that `Expr`, represented with an index
#check Expr.fvar -- named variable in the context
#check Expr.mvar -- metavariable
#check Expr.const -- a defined constant

-- Moreover, user facing names of free variables and metavariables are not a unique
-- identifier of a variable - Lean wants to allow multiple variables with the same name.
-- So, free variables are identified by
#check FVarId
-- and metavariables are identified by
#check MVarId
-- these datatypes hide a name inside too but that name (such as `_uniq.13541`)
-- should never be ever exposed to the user.

/-
### Showing / printing.
Our basic printing function `logInfo` is a bit fancier that a you might expect.
In normal programming languages, we are used to a print function that takes a `String`.
However, in Lean, `logInfo` takes a `Lean.MessageData`. This means that it can show a term
with mouse hover showing types and ctrl+click to go to definitions.
-/
#check MessageData -- interactive expression
#check String -- standard list of characters
#check Format -- string with information about how to line-wrap nicely

-- Examine the print of the following logInfo.
example : True := by
  run_tac
    logInfo m!"Interactive MessageData: t2 = {t2}"
    logInfo s!"String: t2 = {t2}"
    -- the function `repr` allows us to print the underlying data type.
    -- it returns a `Format`.
    logInfo f!"Format : repr t2 = {repr t2}"
  trivial

/-
## (4) Basic API to modify the proof state

Let us write the code for the 4 tactics used in
-/
#check p_imp_p_true
example (p : Prop) : p → p ∧ True := by
  intro h; constructor; assumption; trivial

/-
A lot of the functions / types are hidden in namespaces
* Lean
* Lean.Meta
* Lean.Elab.Tactic
so let's open them
-/

open Lean Meta Elab.Tactic Qq

-- The easiest tactic to replace is "trivial"
def runTrivial0 : TacticM Unit := do
  -- we retrieve the metavariable representing the current goal
  let goal : MVarId ← getMainGoal
  -- and assign it to be True.intro
  goal.assign q(True.intro) -- !!! first attempt, not ideal
  -- better to avoid low-level `MVarId.assign`, we will see why

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
MVarId.assign happily closed the goal. Then we correctly closed the goal
`?right : True`, and at the very end, after the Lean kernel checked
the entire proof term, we got a mysterious error that we cannot apply
`@And.intro p True` to `True.intro` because it expects a proof of `p`,
and not a proof of `True`.

Such errors are hard to decode, so it is better to ensure that we only
assign a metavariable if the assignment has the correct type.
Fortunately, Batteries has a function that checks if something can be assigned.
ctrl+click on it to see the implementation.
-/
#check MVarId.assignIfDefEq

-- version throwing an error if the goal isn't `True`
def runTrivial1 : TacticM Unit := do
  -- we retrieve the metavariable represesnting the current goal
  let goal : MVarId ← getMainGoal
  -- and assign it to be True.intro
  goal.assignIfDefEq q(True.intro)

-- now we get an error in the correct place if we try to run `runTrivial1`
-- on the wrong goal
example (p : Prop) : p → p ∧ True := by
  intro h; constructor
  run_tac runTrivial1 -- error where it should be :-)
  run_tac runTrivial1

/-
However, the error message "failed", is not very helpful.
To improve this, we can catch that error, and provide our own, more useful error.
We can catch errors using a `try ... catch _ => ...` block.
And we can throw errors using `throwError`.
-/
def runTrivial : TacticM Unit := do
  -- we retrieve the metavariable represesnting the current goal
  let goal : MVarId ← getMainGoal
  -- and assign it to be True.intro
  try
    goal.assignIfDefEq q(True.intro)
  catch _ =>
    let goalType ← goal.getType
    throwError "tactic runTrivial1 failed, the goal has type `{goalType}` instead of `True`"

example (p : Prop) : p → p ∧ True := by
  intro h; constructor
  run_tac runTrivial -- now we get a useful error message here
  run_tac runTrivial


/-
To implement `assumption`, we want to loop through all the assumptions,
and try to use them one by one.
The list of assumptions, which appears above the `⊢` in the infoview, is called
the local context. How do we get the local context? In general each metavariable
(i.e. goal) has its own local context, but we can just use `withMainContext`.
This puts the local context of the current goal into the monadic context,
and then we can retrieve the context using `getLCtx`

First, we can just print the assumptions.
-/

example (n : Nat) (hn : n > 5) : True := by
  run_tac
    -- Note: You will see _example in the list, which is there in case
    -- we wanted to build a recursive definition
    withMainContext do
      let ctx ← getLCtx
      -- go through all local declarations
      for (decl : LocalDecl) in ctx do
        logInfo m!"{Expr.fvar decl.fvarId} : {decl.type}  -- {repr decl.kind}"
  trivial

-- We have all the components, so let's implement the assumption tactic.

def runAssumption : TacticM Unit := -- we don't have to start with do here (but can)
  withMainContext do -- but have to "do" it here
    let goal ← getMainGoal
    let ctx ← getLCtx
    for (decl : LocalDecl) in ctx do
      if decl.kind != .default then continue
      try
        goal.assignIfDefEq (Expr.fvar decl.fvarId)
        return -- if succeeded, we are done
      catch _ =>
        pure () -- ignore the exception
    throwError "Assumption not found"

-- let's test
example (p : Prop) : p → p ∧ True := by
  intro h; constructor
  run_tac runAssumption
  run_tac runTrivial

/-
The remaining two tactics require creating a new metavariable.
A new metavariable is created using
-/
#check mkFreshExprMVar
/-
However a good practice is to make the goal variables "syntheticOpaque" - then Lean
knows that they are somewhat important, and doesn't assign them willy-nilly.

One way is to use the following function
-/
#check mkFreshExprSyntheticOpaqueMVar
/-
although if you Ctrl-click on it, you find that it just
calls `mkFreshExprMVar` with a specific kind.
-/

/-
Now let us define `runConstructor`, in which we will decompose `And`.
(we will not attempt general constructor)
First, we just write the function that reads the type `A ∧ B` from the goal,
and extracts the two type expressions `A` and `B`.
-/
def extractAndGoals1 : TacticM (Expr × Expr) := do
  let tgt ← getMainTarget -- equivalent to `(← getGoal).getType`
   -- add a `Q(...)` annotation to `tgt`, !! must use `have`, not `let`
  have quotedTgt : Q(Prop) := tgt
  match quotedTgt with
  | ~q($p ∧ $q) => -- Qq match, must run in MetaM or higher
    return (p, q)
  | _ => throwError "Goal {tgt} is not of the form (?_ ∧ ?_)"

-- Qq is handy but it is worth knowing how to do these things "manually"
def extractAndGoals2 : TacticM (Expr × Expr) := do
  let tgt ← getMainTarget
  -- an alternative syntax to match ... with
  let (`And, #[p, q]) := tgt.getAppFnArgs
    | throwError "Goal {tgt} is not of the form (?_ ∧ ?_)"
  return (p, q)
-- Note that the non-Qq version requires the term to be more "exactly matching".
-- Before matching, you might want to call the following two functions
#check instantiateMVars
#check whnf
-- however digging deeper into them exceeds the scope of this tutorial.

-- let's check that our decomposition of "And" works.
example (p q : Prop) (h : p ∧ q) : p ∧ q := by
  run_tac
    let (a1, b1) ← extractAndGoals1
    logInfo m!"Qq extraction: {a1} AND {b1}"
    let (a2, b2) ← extractAndGoals2
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
    let left : Q($a) ← mkFreshExprSyntheticOpaqueMVar a (tag := `left) -- build new metavariables
    let right : Q($b) ← mkFreshExprSyntheticOpaqueMVar b (tag := `right)
    goal.assign q(And.intro $left $right) -- can we be brave here with `.assign`? :-)
    -- the list of active goals is not maintained automatically,
    -- we need to tell the proof state that we created two new goals
    replaceMainGoal [left.mvarId!, right.mvarId!]

-- let's test
example (p : Prop) : p → p ∧ True := by
  intro h;
  run_tac runConstructor
  run_tac runAssumption
  run_tac runTrivial

/-
The implementation of intro has the most hidden intricacies. Do not worry
too much if you don't fully understand it.
-/
def runIntro (name : Name) : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let lctx ← getLCtx
    let .forallE _ type body c ← goal.getType
      | throwError "Goal not of the form `_ → _` or `∀ _, _`"
    let fvarId : FVarId ← mkFreshFVarId -- allocate new variable
    let lctx' := lctx.mkLocalDecl fvarId name type c -- put into a new context
    let fvar : Expr := .fvar fvarId
    let body := body.instantiate1 fvar -- convert bvar to fvar
    withLCtx' lctx' do
      -- `mkFreshExprSyntheticOpaqueMVar` uses the monadic context to determine the
      -- local context of the new metavariable
      let newMVar ← mkFreshExprSyntheticOpaqueMVar body
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
to the local context -- a custom "have"
-/
example (a b : Prop) (ha : a) (hab : a → b) : b := by
  run_tac -- we want to emulate: "have hb := hab ha"
    withMainContext do
      let goal ← getMainGoal
      let lctx ← getLCtx
      -- find appropriate free variables
      let some ehab := lctx.findFromUserName? `hab | throwError "hab not found"
      let some eha := lctx.findFromUserName? `ha | throwError "ha not found"
      let e : Expr := (.app -- build the term "hab ha"
        (.fvar ehab.fvarId)
        (.fvar eha.fvarId)
      )
      let t ← inferType e -- t = "b", e = "hab hb"
      -- goal: ctx ⊢ mainGoal
      let goal2 ← goal.assert `hb t e
      -- goal2: ctx ⊢ t -> mainGoal
      let (_, goal3) ← goal2.intro `hb
      -- goal3: ctx, t ⊢ mainGoal
      replaceMainGoal [goal3]
  exact hb

/-
## (5) How to declare syntax for a new tactic

So far, we have discussed how tactics work internally, but another important part of
tactics is the syntax that we use to call them. When dealing with syntax,
we use the types `Lean.Syntax` and `Lean.TSyntax`. Don't worry about the implementation
of `Lean.Syntax`, as it is quite messy.
-/
#check Lean.Syntax
#check Lean.TSyntax
/--
Just like `Q(...)` is an annotated version of `Expr`, `TSyntax ..` is an annotated version
of `Syntax`. However, syntax annotations (so called syntax categories) are just a `Name`.
The most common ones are
- `term`, which represents a lean expression (of any type)
- `tactic`, which represents a tactic
- `num`, which represents a natural number literal
- `ident`, which represents a name/identifier literal
Other less important examples of syntax categories include
- `command`, which represents a top-level command (e.g. `def ..` or `#eval ..`)
- `doElem`, which represent a command in "do notation"

We can construct `Syntax` using quotations like `` `(kind| syntax)``. This only works
in a monad similar to `MetaM` (above `CoreM` to be precise).
-/
def s1 : MetaM (TSyntax `tactic) := `(tactic| apply And.intro)
def s2 : MetaM (TSyntax `term) := `(1+2+3) -- equivalent to `(term| 1+2+3)

-- As you can see, the produced `Syntax` is quite messy; but all the data is somewhere inside
#eval s1
#eval s2

/-
Now that we can construct syntax, we can make a macro. A macro is a rule that operates on
syntax, and these rules are used when the syntax is being elaborated.
-/

/-- `my_constructor` is a version of `constructor` that only applies to `And` goals -/
macro "my_constructor" : tactic => `(tactic| apply And.intro)
/-- `my_trivial` solves goal `True` -/
macro "my_trivial" : tactic => `(tactic| exact True.intro)

-- note that by hovering you can see the doc-strings of the macros
example (p : Prop) : p → p ∧ True := by
  intro h; my_constructor; assumption; my_trivial

/-
For `intro` and `assumption`, we show how to assign the monadic programs
to the appropriate syntax using the `elab` command.

Be aware that the syntax-defining syntax is quite sensitive to whitespace characters.
In the following example, you cannot put a space between `a` and `:`.
Also, the `` `(tactic| `` notation as shown earlier is best kept without spaces.
-/

/-- Our variant of `intro`. -/
elab "my_intro" a:ident : tactic => do
  -- `a` has type ``TSyntax `ident``. This is the syntax kind for identifiers
  let aName : Name := a.getId
  runIntro aName

/-- Our variant of `assumption`. -/
elab "my_assumption" : tactic => do
  runAssumption

example (p : Prop) : p → p ∧ True := by
  my_intro h; my_constructor; my_assumption; my_trivial

/-
Let us show how to extract more kinds of arguments from Syntax
with the following example tactics.
-/

/-- Print a string as a message -/
elab "echo" s:str : tactic => do
  -- convert ``TSyntax `str`` to `String`
  let s : String := s.getString
  Lean.logInfo s

/-- Print a square of a given natural number -/
elab "square_nat" n:num : tactic => do
  -- convert ``TSyntax `num`` to `Nat`
  let n : Nat := n.getNat
  Lean.logInfo s!"{n^2}"

/-- Print a square of a given non-negative decimal number -/
elab "square_float" n:scientific : tactic => do
  let (m,s,e) := n.getScientific
  let q : Rat := Rat.ofScientific m s e
  let f : Float := Float.ofScientific m s e
  Lean.logInfo s!"Rat: {q*q}, Float: {f^2}"
-- Note: negative numbers are not supported as native syntax.

/-- Display a type of a given term -/
elab "my_check" e:term : tactic => do
  withMainContext do -- term parsing can depend on the context
    -- convert ``TSyntax `term`` to `Expr`, without a given expected type
    let e : Expr ← elabTerm e none
    -- Note that there are many analogous `Lean.Elab.Tactic.elab*`
    -- such as `elabTermEnsuringType`, `elabTermWithHoles`...
    let t ← inferType e
    Lean.logInfo m!"{e} : {t}"

example (n : Nat) : True := by
  echo "Hello world!"
  square_nat 5
  square_float 0.5
  my_check n+5
  trivial

elab "my_have" n:ident ":=" e:term : tactic => do
  throwError "Not implemented, left as an exercise"

example (x y : Prop) (hx : x) (hxy : x → y) : y := by
  my_have hy := hxy hx
  exact hy

/-
The `macro` and `elab` commands are nice, but for more complicated syntax, you may need
a bit more flexibility. This can be achieved by first defining the syntax with a
`syntax` command, and then defining the meaning of that syntax with a `macro_rules` or
`elab_rules` command. For example, the above tactics can be defined as follows:
-/

/-- Doc-string for `my_constructor'`. -/
syntax "my_constructor'" : tactic
syntax "my_trivial'" : tactic
syntax "my_intro'" ident : tactic
syntax "my_assumption'" : tactic

macro_rules
| `(tactic| my_constructor') => `(tactic| apply And.intro)
| `(tactic| my_trivial')     => `(tactic| exact True.intro)

elab_rules : tactic
-- to match a variable, we use the `$` anti-quotation.
-- we can optionally annotate the syntax kind `ident` with `$h:ident` instead of `$h`.
| `(tactic| my_intro' $h:ident) => runIntro h.getId
| `(tactic| my_assumption') => runAssumption

example (p : Prop) : p → p ∧ True := by
  my_intro' h; my_constructor'; my_assumption'; my_trivial'

/-
For example, these `macro_rules` come in handy when working with syntax arrays.
To illustrate this, let's define a simple form of the `simp_rw` tactic.
We will use the syntax kind `Lean.Parser.Tactic.location`, so let's open the namespace:
-/
open Parser.Tactic
syntax "my_simp_rw " "[" term,* "]" (location)? : tactic
/-
In the syntax `term,*`
- `*` signifies that it is a possibly empty list. `+` instead gives a nonempty list.
- `,` signifies that it is a comma-separated list. Omitting the `,` gives a space separated list.
In the syntax `(Parser.Tactic.location)?`
- `Parser.Tactic.location` is the syntax of specifying a hypothesis (like in `simp at h`)
- `(...)?` means that the inner syntax is optional: either it is there or it isn't

Now we can use `macro_rules` to define the tactic
-/

macro_rules
/-
To match optional syntax, or a list of syntax, we use the `$[...]` anti-quotation.
- `$[...]?` matches optional syntax
- `$[...],*` matches a possibly empty comma-separated list of syntax
Square brackets without a dollar represent explicit `[` and `]` symbols in the syntax.
Not all syntax kind annotations are required here. They have been added for clarity.
-/
| `(tactic| my_simp_rw [$e:term, $[$es:term],*] $[$loc:location]?) =>
  `(tactic| simp only [$e:term] $[$loc:location]?; my_simp_rw [$[$es:term],*] $[$loc:location]?)
| `(tactic| my_simp_rw [$e:term] $[$loc:location]?) => `(tactic| simp only [$e:term] $[$loc:location]?)
| `(tactic| my_simp_rw [] $[$_loc:location]?) => `(tactic| skip)

-- Let's test it
example : ∀ n m : Nat, m + n + 1 - 1 = n + m := by
  my_simp_rw [Nat.add_one_sub_one, Nat.add_comm, implies_true]

-- or we can use `elab_rules` to loop through the array of terms directly

syntax "my_simp_rw' " "[" term,* "]" (Parser.Tactic.location)? : tactic

elab_rules : tactic
| `(tactic| my_simp_rw' [$[$es:term],*] $[$loc:location]?) =>
  for e in es do
    let simpOnlyTactic ← `(tactic| simp only [$e:term] $[$loc:location]?)
    evalTactic simpOnlyTactic

-- Let's test it
example : ∀ n m : Nat, m + n + 1 - 1 = n + m := by
  my_simp_rw' [Nat.add_one_sub_one, Nat.add_comm, implies_true]

/-
As you can see, the syntax matching can get quite complicated. Unfortunately there is
no universal guide on these intricacies

Here are some more advanced things you can do:
-/

-- ### Defining syntax
-- we could have defined the `my_simp_rw` syntax like this instead:
syntax rwRule := ("← " <|> "<- ")? term
syntax rwRuleSeq := "[" rwRule,* "]"
syntax "my_simp_rw " rwRuleSeq (location)? : tactic

-- ### Defining a syntax category
-- As a toy example, if you want to be able to write terms in natural language

declare_syntax_cat my_syntax_cat

syntax my_syntax_cat " plus " my_syntax_cat : my_syntax_cat
syntax my_syntax_cat " times " my_syntax_cat : my_syntax_cat
syntax "(" my_syntax_cat ")" : my_syntax_cat
syntax num : my_syntax_cat -- the `num` syntax category is used for number literals like `42`
syntax "language[" my_syntax_cat "]" : term

macro_rules
| `(language[$a plus $b]) => `(language[$a] + language[$b])
| `(language[$a times $b]) => `(language[$a] * language[$b])
| `(language[($a)])    => `((language[$a]))
| `(language[$n:num])  => `($n:num)

/-
If we now write down the term `language[1 plus (2 times 4)]`,
then the `macro_rules` will turn this into `1 + (2 * 4)`.
-/
#check (language[1 plus (2 times 4)] : Int)

/-
## Finishing notes

There is much more to say,
You can check out a more advanced Lean Metaprogramming book
https://leanprover-community.github.io/lean4-metaprogramming-book/
Another nice resource of what could be a problem when you get stuck
on a mysterious metaprogramming bug:
https://github.com/leanprover-community/mathlib4/wiki/Metaprogramming-gotchas
You can also learn more about Qq on its own github
https://github.com/leanprover-community/quote4

But also, just be curious - ctrl-click on the functions we are using
to see what they are doing.

You can also ctrl-click on a monad, such as `TacticM` or `MetaM`
(and others you may run into such as `TermElabM`, `CoreM`, `IO`, `MacroM`, `DelabM`),
and you will see the extra states it has (as `Context` & `State`), as well as
what other monad it extends, if any.
These states can be a bit scary but all the information Lean
has to its disposal must be somewhere in them...
-/
end MetaProgrammingTutorial
