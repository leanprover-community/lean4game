import NNG.Levels.Inequality.Level_1
-- import NNG.Levels.Inequality.Level_2
-- import NNG.Levels.Inequality.Level_3
-- import NNG.Levels.Inequality.Level_4
-- import NNG.Levels.Inequality.Level_5
-- import NNG.Levels.Inequality.Level_6
-- import NNG.Levels.Inequality.Level_7
-- import NNG.Levels.Inequality.Level_8
-- import NNG.Levels.Inequality.Level_9
-- import NNG.Levels.Inequality.Level_10
-- import NNG.Levels.Inequality.Level_11
-- import NNG.Levels.Inequality.Level_12
-- import NNG.Levels.Inequality.Level_13
-- import NNG.Levels.Inequality.Level_14
-- import NNG.Levels.Inequality.Level_15
-- import NNG.Levels.Inequality.Level_16
-- import NNG.Levels.Inequality.Level_17

Game "NNG"
World "Inequality"
Title "Inequality World"

Introduction
"
A new import, giving us a new definition. If `a` and `b` are naturals,
`a ≤ b` is *defined* to mean

`∃ (c : mynat), b = a + c`

The upside-down E means \"there exists\". So in words, $a\\le b$
if and only if there exists a natural $c$ such that $b=a+c$. 

If you really want to change an `a ≤ b` to `∃ c, b = a + c` then
you can do so with `rw le_iff_exists_add`:

```
le_iff_exists_add (a b : mynat) :
  a ≤ b ↔ ∃ (c : mynat), b = a + c
```

But because `a ≤ b` is *defined as* `∃ (c : mynat), b = a + c`, you
do not need to `rw le_iff_exists_add`, you can just pretend when you see `a ≤ b`
that it says `∃ (c : mynat), b = a + c`. You will see a concrete
example of this below.

A new construction like `∃` means that we need to learn how to manipulate it.
There are two situations. Firstly we need to know how to solve a goal
of the form `⊢ ∃ c, ...`, and secondly we need to know how to use a hypothesis
of the form `∃ c, ...`. 
"