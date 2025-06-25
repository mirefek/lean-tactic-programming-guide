/-
# (1) What simp & rw do on proof term level, and what is the difference?

TODO: explain how we are examining `rw` & `simp`, and what we are demonstrating
with the examples.
-/

theorem rw_example (a b : Nat) (f : Nat → Nat) (p : Nat → Prop)
    (h_rw  : ∀ x : Nat, f x = x) (h_finish : p (a + b + a + b)) :
    p (f a + f b + f a + f b) := by
  rw [h_rw]
  rw [h_rw]
  exact h_finish

#print rw_example
#check Eq.mpr
#check congrArg

theorem rw_example2 : ∀ (a b : Nat) (f : Nat → Nat) (p : Nat → Prop),
  (∀ (x : Nat), f x = x) → p (a + b + a + b) → p (f a + f b + f a + f b) :=
fun a b f p h_rw h_finish =>
  Eq.mpr (id (congrArg (fun X => p (X + f b + X + f b)) (h_rw a)))
    (Eq.mpr (id (congrArg (fun X => p (a + X + a + X)) (h_rw b))) h_finish)

-- TODO: the retyping role of `id`, which metaprogramming function
-- actually constructed `id` in `rw`?
def x : (fun t _ => t) Nat 8 := 4
#check x
#check (x : Nat)
#check (id x : Nat)
#check @id Nat x

theorem simp_example (a b c : Nat) (f : Nat → Nat) (p : Nat → Prop)
    (h_rw  : ∀ x : Nat, f x = x) (h_finish : p (a + c + b + c + a + c)) :
    p (f a + c + f b + c + f a + c) := by
  simp only [h_rw]
  exact h_finish

#print simp_example
#check congr

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
