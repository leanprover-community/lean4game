import NNG.Metadata
import NNG.MyNat.AdvAddition

Game "NNG"
World "AdvAddition"
Level 13
Title "ne_succ_self"

open MyNat

Introduction
"
The last level in Advanced Addition World is the statement
that $n\\not=\\operatorname{succ}(n)$. When you've done this
you've completed Advanced Addition World and can move on
to Advanced Multiplication World (after first doing
Multiplication World, if you didn't do it already). 
"

Statement --ne_succ_self
"For any natural number $n$, we have
$$ n \\neq \\operatorname{succ}(n). $$"
     (n : ℕ) : n ≠ succ n := by
  induction n with d hd
  apply zero_ne_succ
  intro hs
  apply hd
  apply succ_inj
  assumption

Conclusion
"

"
