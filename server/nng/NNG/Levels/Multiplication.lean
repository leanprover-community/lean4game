import NNG.Levels.Multiplication.Level_1
import NNG.Levels.Multiplication.Level_2
import NNG.Levels.Multiplication.Level_3
import NNG.Levels.Multiplication.Level_4
import NNG.Levels.Multiplication.Level_5
import NNG.Levels.Multiplication.Level_6
import NNG.Levels.Multiplication.Level_7
import NNG.Levels.Multiplication.Level_8
import NNG.Levels.Multiplication.Level_9


Game "NNG"
World "Multiplication"
Title "Multiplication World"

Introduction
"
In this world you start with the definition of multiplication on `ℕ`. It is
defined by recursion, just like addition was. So you get two new axioms:

  * `mul_zero (a : ℕ) : a * 0 = 0`
  * `mul_succ (a b : ℕ) : a * succ b = a * b + a`

In words, we define multiplication by \"induction on the second variable\",
with `a * 0` defined to be `0` and, if we know `a * b`, then `a` times
the number after `b` is defined to be `a * b + a`.

You can keep all the theorems you proved about addition, but
for multiplication, those two results above are what you've got right now.

So what's going on in multiplication world? Like addition, we need to go
for the proofs that multiplication
is commutative and associative, but as well as that we will
need to prove facts about the relationship between multiplication
and addition, for example `a * (b + c) = a * b + a * c`, so now
there is a lot more to do. Good luck!
"