import NNG.Metadata
import NNG.MyNat.Multiplication
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "NNG"
World "AdvMultiplication"
Level 4
Title "mul_left_cancel"

open MyNat

Introduction
"
This is the last of the bonus multiplication levels.
`mul_left_cancel` will be useful in inequality world.

People find this level hard. I have probably had more questions about this
level than all the other levels put together, in fact. Many levels in this
game can just be solved by \"running at it\" -- do induction on one of the
variables, keep your head, and you're done. In fact, if you like a challenge,
it might be instructive if you stop reading after the end of this paragraph and try solving this level now by induction,
seeing the trouble you run into, and reading the rest of these comments afterwards. This level
has a sting in the tail. If you are a competent mathematician, try
and figure out what is going on. Write down a maths proof of the
theorem in this level. Exactly what statement do you want to prove
by induction? It is subtle.

Ok so here are some spoilers. The problem with naively running at it, is that if you try induction on,
say, $c$, then you are imagining a and b as fixed, and your inductive
hypothesis $P(c)$ is $ab=ac \\implies b=c$. So for your inductive step
you will be able to assume $ab=ad \\implies b=d$ and your goal will
be to show $ab=a(d+1) \\implies b=d+1$. When you also assume $ab=a(d+1)$
you will realise that your inductive hypothesis is *useless*, because
$ab=ad$ is not true! The statement $P(c)$ (with $a$ and $b$ regarded
as constants) is not provable by induction.

What you *can* prove by induction is the following *stronger* statement.
Imagine $a\not=0$ as fixed, and then prove \"for all $b$, if $ab=ac$ then $b=c$\"
by induction on $c$. This gives us the extra flexibility we require.
Note that we are quantifying over all $b$ in the inductive hypothesis -- it
is essential that $b$ is not fixed. 

You can do this in two ways in Lean -- before you start the induction
you can write `revert b,`. The `revert` tactic is the opposite of the `intro`
tactic; it replaces the `b` in the hypotheses with \"for all $b$\" in the goal.

Alternatively, you can write `induction c with d hd
generalizing b` as the first line of the proof. 

If you do not modify your technique in this way, then this level seems
to be impossible (judging by the comments I've had about it!)
"

Statement
"If $a \\neq 0$, $b$ and $c$ are natural numbers such that
$ ab = ac, $
then $b = c$."
    (a b c : ℕ) (ha : a ≠ 0) : a * b = a * c → b = c := by
  sorry

Conclusion
"

"
