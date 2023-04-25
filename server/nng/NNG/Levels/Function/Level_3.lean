import NNG.Metadata

Game "NNG"
World "Function"
Level 3
Title "the have tactic"

open MyNat

Introduction
"
Say you have a whole bunch of sets and functions between them,
and your goal is to build a certain element of a certain set.
If it helps, you can build intermediate elements of other sets
along the way, using the `have` command. `have` is the Lean analogue
of saying \"let's define an element $q\\in Q$ by...\" in the middle of a calculation.
It is often not logically necessary, but on the other hand
it is very convenient, for example it can save on notation, or
it can break proofs or calculations up into smaller steps.

In the level below, we have an element of $P$ and we want an element
of $U$; during the proof we will make several intermediate elements
of some of the other sets involved. The diagram of sets and
functions looks like this pictorially:

$$
\\begin{CD}
  P  @>{h}>> Q       @>{i}>> R \\\\
  @.         @VV{j}V           \\\\
  S  @>>{k}> T       @>>{l}> U
\\end{CD}
$$

and so it's clear how to make the element of $U$ from the element of $P$.
"

Statement
"Given an element of $P$ we can define an element of $U$."
    (P Q R S T U: Type) (p : P) (h : P → Q) (i : Q → R) (j : Q → T) (k : S → T) (l : T → U) :
    U := by
  Hint "Indeed, we could solve this level in one move by typing

  ```
  exact l (j (h p))
  ```

  But let us instead stroll more lazily through the level.
  We can start by using the `have` tactic to make an element of $Q$:

  ```
  have q := h p
  ```
  "
  Branch
    exact l (j (h p))
  have q := h p
  Hint "
  and now we note that $j(q)$ is an element of $T$

  ```
  have t : T := j q
  ```

  (notice how we can explicitly tell Lean
  what set we thought $t$ was in, with that `: T` thing before the `:=`.
  This is optional unless Lean can not figure it out by itself.)
  "
  have t : T := j q
  Hint "
  Now we could even define $u$ to be $l(t)$:

  ```
  have u : U := l t
  ```
  "
  have u : U := l t
  Hint "…and then finish the level with `exact u`."
  exact u

NewTactic «have»

Conclusion
"
If you solved the level using `have`, then you might have observed
that before the final step the context got quite messy by all the intermediate
variables we introduced. You can click \"Toggle Editor\" and then move the cursor
around to see the proof you created.

The context was already bad enough to start with, and we added three more
terms to it. In level 4 we will learn about the `apply` tactic
which solves the level using another technique, without leaving
so much junk behind.
"
