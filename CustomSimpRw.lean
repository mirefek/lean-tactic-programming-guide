import Lean
import Qq

open Lean Elab Meta Tactic
open Qq

/-
# Writing rw / simp from scratch

Content
(1) What simp & rw do on proof term level, and what is the difference?
(2) Implementing basic `simp` & `rw` prototypes.
(3) Unification -- rewriting a quantified equality.
(4) Context & digging into quantifiers with simp.
(5) Collecting tagged lemmas
(6) Simplification procedures - building upon existing simp infrastructure
-/

/-
# (1) What simp & rw do on proof term level, and what is the difference?

You probably know that the main difference between `simp only` and `rw` is
that `simp only` rewrites as long as it can, while `rw` rewrites just once.

The background reason is a fundamental differences between the terms
proof produced.

## rw
Let as look at an example proof using `rw`.
-/

theorem rw_example (a b : Nat) (f : Nat → Nat) (p : Nat → Prop)
    (h_rw  : ∀ x : Nat, f x = x) (h_finish : p (a + b + a + b)) :
    p (f a + f b + f a + f b) := by
  rw [h_rw] -- rewrites two instances of `f a`
  rw [h_rw] -- rewrites two instances of `f b`
  exact h_finish

-- and print its proof term
#print rw_example

-- it should look similar to
example : ∀ (a b : Nat) (f : Nat → Nat) (p : Nat → Prop),
  (∀ (x : Nat), f x = x) → p (a + b + a + b) → p (f a + f b + f a + f b) :=
fun a b f p h_rw h_finish =>
  Eq.mpr (
    congrArg (fun X => p (X + f b + X + f b)) (h_rw a : f a = a)
    : p (f a + f b + f a + f b) = p (a + f b + a + f b)
  )
  (Eq.mpr (
    congrArg (fun X => p (a + X + a + X)) (h_rw b : f b = b)
    : p (a + f b + a + f b) = p (a + b + a + b)
  ) h_finish)

-- You can see two main theorems used for each rewrite:
#check congrArg -- digging into a subterm
#check Eq.mpr -- finishing the proof

#print Eq.rec
#print Eq.ndrec
#print Eq.mp
#print cast

/-
Because of the theorems that `rw` is using, it first instantiates
the hypothesis `h_rw`, and then replaces all the instances in the goal
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
## simp

Simp doesn't do all its equal rewrites in one go.
Instead, it recursively dives into the term, and when
it combines two branches in which both terms got
updated, it directly uses
-/
#check congr

theorem simp_example (a b c : Nat) (f : Nat → Nat) (p : Nat → Prop)
    (h_rw  : ∀ x : Nat, f x = x) (h_finish : p (a + c + b + c + a + c)) :
    p (f a + c + f b + c + f a + c) := by
  simp only [h_rw]
  exact h_finish

#print simp_example

/-
After some prettification, you could get the following term.
-/
theorem simp_example2 (a b c : Nat) (f : Nat → Nat) (p : Nat → Prop)
    (h_rw  : ∀ x : Nat, f x = x) (h_finish : p (a + c + b + c + a + c)) :
    p (f a + c + f b + c + f a + c) :=
  Eq.mpr
  (congrArg (fun x => p (x + c))
    (congr
      (congrArg (fun x => (x + c + ·))
        (congr
          (congrArg
            (fun x => (x + c + ·)) (h_rw a : f a = a)
            : (f a + c + ·) = (a + c + ·)
          )
          (h_rw b : f b = b)
          : f a + c + f b = a + c + b)
        : (f a + c + f b + c + ·) = (a + c + b + c + ·)
      )
      (h_rw  a : f a = a)
      : f a + c + f b + c + f a = a + c + b + c + a)
    : p (f a + c + f b + c + f a + c) = p (a + c + b + c + a + c)
  )
  h_finish
/-
It is not as clean as with `rw`, but you can notice that
* The expression is build gradually, not in one go.
* We actually run `h_rw a` twice in the proof term, because
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
# (2) Implementing basic `simp` & `rw` prototypes.

In the basic version, we will be only rewriting the a term
with a single equality without quantifiers. The simp would
process the term recursively but perhaps without repeated call
to itself?
-/

#check kabstract

-- TODO:
-- rw: implement variable extraction (or point to Lean implementation,
-- is it simple enough?) & full tactic replacing the goal
-- from that point on, we should only focus on a given term `t`,
-- with the intention to rewrite `t` to `s`, and give a proof of `t = s`.
-- And implement recursive simp of that form.

/-
# (3) Unification -- rewriting a quantified equality.
-/

-- TODO:
-- basics of unification theory (first-order in almost linear time,
--   second order undecidable, but lean has some heuristics)
-- in practice
-- * replace forall with metavariables
-- * explain & run isDefEq

/-
# (4) Context & digging into quantifiers with simp.
-/

-- extensionality axiom
-- translating between bvars & fvars

/-
# (5) Collecting tagged lemmas
-/

-- TODO

/-
# (6) Simplification procedures - building upon existing simp infrastructure
-/

-- TODO
