import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 4
Title "apply"

open MyNat

Introduction
"
Let's do the same level again:

$$
\\begin{CD}
  P  @>{h}>> Q       @>{i}>> R \\\\
  @.         @VV{j}V           \\\\
  S  @>>{k}> T       @>>{l}> U
\\end{CD}
$$

We are given a proof $p$ of $P$ and our goal is to find a proof of $U$, or
in other words to find a path through the maze that links $P$ to $U$.
In level 3 we solved this by using `have`s to move forward, from $P$
to $Q$ to $T$ to $U$. Using the `apply` tactic we can instead construct
the path backwards, moving from $U$ to $T$ to $Q$ to $P$.
"

Statement
"We can solve a maze."
    (P Q R S T U: Prop) (p : P) (h : P → Q) (i : Q → R)
    (j : Q → T) (k : S → T) (l : T → U) : U := by
  Hint "Our goal is to prove $U$. But $l:T\\implies U$ is
  an implication which we are assuming, so it would suffice to prove $T$.
  Tell Lean this by starting the proof below with

  ```
  apply l
  ```
  "
  apply l
  Hint "Notice that our assumptions don't change but *the goal changes*
  from `U` to `T`.

  Keep `apply`ing implications until your goal is `P`, and try not
  to get lost!"
  Branch
    apply k
    Hint "Looks like you got lost. \"Undo\" the last step."
  apply j
  apply h
  Hint "Now solve this goal
  with `exact p`. Note: you will need to learn the difference between
  `exact p` (which works) and `exact P` (which doesn't, because $P$ is
  not a proof of $P$)."
  exact p

DisabledTactic «have»
