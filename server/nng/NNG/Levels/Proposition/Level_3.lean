import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 3
Title "have"

open MyNat

Introduction
"
Say you have a whole bunch of propositions and implications between them,
and your goal is to build a certain proof of a certain proposition.
If it helps, you can build intermediate proofs of other propositions
along the way, using the `have` command. `have q : Q := ...` is the Lean analogue
of saying \"We now see that we can prove $Q$, because...\"
in the middle of a proof.
It is often not logically necessary, but on the other hand
it is very convenient, for example it can save on notation, or
it can break proofs up into smaller steps.

In the level below, we have a proof of $P$ and we want a proof
of $U$; during the proof we will construct proofs of
of some of the other propositions involved. The diagram of
propositions and implications looks like this pictorially:

$$
\\begin{CD}
  P  @>{h}>> Q       @>{i}>> R \\\\
  @.         @VV{j}V           \\\\
  S  @>>{k}> T       @>>{l}> U
\\end{CD}
$$

and so it's clear how to deduce $U$ from $P$.

"

Statement
"In the maze of logical implications above, if $P$ is true then so is $U$."
    (P Q R S T U: Prop) (p : P) (h : P → Q) (i : Q → R)
    (j : Q → T) (k : S → T) (l : T → U) : U := by
  Hint "Indeed, we could solve this level in one move by typing

  ```
  exact l (j (h p))
  ```

  But let us instead stroll more lazily through the level.
  We can start by using the `have` tactic to make a proof of $Q$:

  ```
  have q := h p
  ```
  "
  have q := h p
  Hint "
  and then we note that $j {q}$ is a proof of $T$:

  ```
  have t : T := j {q}
  ```
  "
  have t := j q
  Hint "
  (note how we explicitly told Lean what proposition we thought ${t}$ was
  a proof of, with that `: T` thing before the `:=`)
  and we could even define $u$ to be $l {t}$:

  ```
  have u : U := l {t}
  ```
  "
  have u := l t
  Hint " and now finish the level with `exact {u}`."
  exact u

DisabledTactic apply

Conclusion
"
If you solved the level using `have`, then click on the last line of your proof
(you do know you can move your cursor around with the arrow keys
and explore your proof, right?) and note that the local context at that point
is in something like the following mess:

```
Objects:
  P Q R S T U : Prop
Assumptions:
  p : P
  h : P → Q
  i : Q → R
  j : Q → T
  k : S → T
  l : T → U
  q : Q
  t : T
  u : U
Goal :
  U
```

It was already bad enough to start with, and we added three more
terms to it. In level 4 we will learn about the `apply` tactic
which solves the level using another technique, without leaving
so much junk behind.
"
