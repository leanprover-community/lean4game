import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases

Game "NNG"
World "AdvProposition"
Level 10
Title "Level 10: the law of the excluded middle."

open MyNat

Introduction
"
We proved earlier that `(P → Q) → (¬ Q → ¬ P)`. The converse,
that `(¬ Q → ¬ P) → (P → Q)` is certainly true, but trying to prove
it using what we've learnt so far is impossible (because it is not provable in
constructive logic). For example, after

```
intro h,
intro p,
repeat {rw not_iff_imp_false at h},
```

in the below, you are left with
```
P Q : Prop,
h : (Q → false) → P → false
p : P
⊢ Q
```

The tools you have are not sufficient to continue. But you can just
prove this, and any other basic lemmas of this form like `¬ ¬ P → P`,
using the `by_cases` tactic. Instead of starting with all the `intro`s,
try this instead:

`by_cases p : P; by_cases q : Q,`

**Note the semicolon**! It means \"do the next tactic to all the goals, not just the top one\".
After it, there are four goals, one for each of the four possibilities PQ=TT, TF, FT, FF.
You can see that `p` is a proof of `P` in some of the goals, and a proof of `¬ P` in others.
Similar comments apply to `q`. 

`repeat {cc}` then finishes the job.

This approach assumed that `P ∨ ¬ P` was true; the `by_cases` tactic just does `cases` on
this result. This is called the law of the excluded middle, and it cannot be proved just
using tactics such as `intro` and `apply`.
"

Statement
"If $P$ and $Q$ are true/false statements, then
$$(\\lnot Q\\implies \\lnot P)\\implies(P\\implies Q).$$ 
"
    (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by
  by_cases p : P
  · by_cases q : Q
    intro h p' -- cc
    assumption
    intro h p'
    have g : ¬ P := h q
    contradiction
  · by_cases q : Q
    intro h p
    assumption
    intro h p
    contradiction

Conclusion
"
OK that's enough logic -- now perhaps it's time to go on to Advanced Addition World!
Get to it via the main menu.

## Pro tip

In fact the tactic `tauto!` just kills this goal (and many other logic goals) immediately.

"
