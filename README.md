# Introduction to Tactic Writing in Lean

Originally, this was a single Lean file, later we extended the tutorial with further files with more advanced topics.

If you are a metaprogramming beginner, we recommend to start with `TacticProgrammingGuide.lean`. There are 762 lines coverging the basics of Lean tactic writing.
We assume you already know Lean, and probably use VS Code,
in that case clone this repository, or simply download [the file](TacticProgrammingGuide.lean).

Alternatively, you can also copy it to [Lean 4 Web](https://live.lean-lang.org/) but you will miss the Ctrl-click feature.

We tried to explain all the basic concepts but keep at least the introduction it beginner friendly.
Enjoy learning Lean metaprogramming. If you are getting confused somewhere, it is probably not your fault. Let us know what needs more clarification in the [Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/Introduction.20to.20tactic.20programming/near/524164016).

## Content

So far, there are three tutorials of increasing difficulty. Although you can scroll through it on Github, we indeed recommend to download the files and play with them.
* [Introduction](TacticProgrammingGuide.lean): the basic introduction mentioned above.
  * [How imperative programs work in Lean](TacticProgrammingGuide.lean#L44)
  * [What is a proof state](TacticProgrammingGuide.lean#L127)
  * [Basic data structures around Lean metaprogramming](TacticProgrammingGuide.lean#L155)
  * [Implementing basic tactics](TacticProgrammingGuide.lean#L238)
  * [How to declare syntax for a new tactic](TacticProgrammingGuide.lean#L513)
* [Implementing `rw` from scratch](CustomRw.lean): a tactic that does a single rewrite.
  * [What `rw` does on proof term level](CustomRw.lean#L19)
  * [Implementing basic `rw`](CustomRw.lean#L67)
  * [Options for normalization](CustomRw.lean#L242)
  * [Unification - rewriting a quantified equality.](CustomRw.lean#L313)
* [Implementing `simp` from scratch](CustomSimp.lean): more advanced expression manipulation.
  * [What `simp` does on proof term level](CustomSimp.lean#L22)
  * [Filling implicit arguments](CustomSimp.lean#L83)
  * [Custom SimpResult datastructure](CustomSimp.lean#L187)
  * [Basic `simp` implementation](CustomSimp.lean#L250)
  * [Debugging with traces](CustomSimp.lean#L360)
  * [Implementing `simp` inside binders](CustomSimp.lean#L457)
  * [Collecting tagged lemmas](CustomSimp.lean#L595)
