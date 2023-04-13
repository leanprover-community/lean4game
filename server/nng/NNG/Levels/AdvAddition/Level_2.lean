import NNG.Metadata
import NNG.MyNat.AdvAddition

Game "NNG"
World "AdvAddition"
Level 2
Title "succ_succ_inj"

open MyNat

Introduction
"
In the below theorem, we need to apply `succ_inj` twice. Once to prove
$succ(succ(a))=succ(succ(b))\\implies succ(a)=succ(b)$, and then again
to prove $succ(a)=succ(b)\\implies a=b$. However `succ(a)=succ(b)` is
nowhere to be found, it's neither an assumption or a goal when we start
this level. You can make it with `have` or you can use `apply`.
"

Statement
"For all naturals $a$ and $b$, if we assume $succ(succ(a))=succ(succ(b))$, then we can
deduce $a=b$. "
    {a b : ℕ} (h : succ (succ a) = succ ( succ b )) : a = b := by
  apply succ_inj
  apply succ_inj
  assumption

Conclusion
"
## Sample solutions to this level. 

Make sure you understand them all. And remember that `rw` should not be used
with `succ_inj` -- `rw` works only with equalities or `↔` statements,
not implications or functions.

example {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) :  a = b := 
begin
  apply succ_inj,
  apply succ_inj,
  exact h
end 

example {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) :  a = b := 
begin
  apply succ_inj,
  exact succ_inj(h),
end 

example {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) :  a = b := 
begin
  exact succ_inj(succ_inj(h)),
end 
"
