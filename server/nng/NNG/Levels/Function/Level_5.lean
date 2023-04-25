import NNG.Metadata

Game "NNG"
World "Function"
Level 5
Title "P → (Q → P)"

open MyNat

Introduction
"
In this level, our goal is to construct a function, like in level 2.

```
P → (Q → P)
```

So $P$ and $Q$ are sets, and our goal is to construct a function
which takes an element of $P$ and outputs a function from $Q$ to $P$.
We don't know anything at all about the sets $P$ and $Q$, so initially
this seems like a bit of a tall order. But let's give it a go.
"

Statement
"We define an element of $\\operatorname{Hom}(P,\\operatorname{Hom}(Q,P))$."
    (P Q : Type) : P → (Q → P) := by
  Hint "Our goal is `P → X` for some set $X=\\operatorname\{Hom}(Q,P)$, and if our
  goal is to construct a function then we almost always want to use the
  `intro` tactic from level 2, Lean's version of \"let $p\\in P$ be arbitrary.\"
  So let's start with

  ```
  intro p
  ```"
  intro p
  Hint "
  We now have an arbitrary element $p\\in P$ and we are supposed to be constructing
  a function $Q\to P$. Well, how about the constant function, which
  sends everything to $p$?
  This will work. So let $q\\in Q$ be arbitrary:

  ```
  intro q
  ```"
  intro q
  Hint "and then let's output `p`.

  ```
  exact p
  ```"
  exact p

Conclusion
"

"
