import NNG.Metadata

Game "NNG"
World "Function"
Level 4
Title "the `apply` tactic"

open MyNat

Introduction
"Let's do the same level again:

$$
\\begin{CD}
  P  @>{h}>> Q       @>{i}>> R \\\\
  @.         @VV{j}V           \\\\
  S  @>>{k}> T       @>>{l}> U
\\end{CD}
$$

We are given $p \\in P$ and our goal is to find an element of $U$, or
in other words to find a path through the maze that links $P$ to $U$.
In level 3 we solved this by using `have`s to move forward, from $P$
to $Q$ to $T$ to $U$. Using the `apply` tactic we can instead construct
the path backwards, moving from $U$ to $T$ to $Q$ to $P$.
"

Statement
"Given an element of $P$ we can define an element of $U$."
    (P Q R S T U: Type)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U) : U :=
by
  Hint "Our goal is to construct an element of the set $U$. But $l:T\\to U$ is
  a function, so it would suffice to construct an element of $T$. Tell
  Lean this by starting the proof below with

  ```
  apply l
  ```
  "
  apply l
  Hint "Notice that our assumptions don't change but *the goal changes*
  from `U` to `T`.

  Keep `apply`ing functions until your goal is `P`, and try not
  to get lost!"
  Branch
    apply k
    Hint "Looks like you got lost. \"Undo\" the last step."
  apply j
  apply h
  Hint " Now solve this goal
  with `exact p`. Note: you will need to learn the difference between
  `exact p` (which works) and `exact P` (which doesn't, because $P$ is
  not an element of $P$)."
  exact p

NewTactic apply
DisabledTactic «have»
