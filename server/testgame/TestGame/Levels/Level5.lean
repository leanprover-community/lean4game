import TestGame.Metadata
import TestGame.Tactics

Level 5

Title "The induction_on spell"

Introduction
"
Welcome to Addition World. If you've done all four levels in tutorial world
and know about `rewrite` and `rfl`, then you're in the right place. Here's
a reminder of the things you're now equipped with which we'll need in this world.

## Data:

  * a type called `ℕ`
  * a term `0 : ℕ`, interpreted as the number zero.
  * a function `succ : ℕ → ℕ`, with `succ n` interpreted as \"the number after `n`\".
  * Usual numerical notation 0,1,2 etc (although 2 onwards will be of no use to us until much later ;-) ).
  * Addition (with notation `a + b`).

## Theorems:

  * `add_zero (a : ℕ) : a + 0 = a`. Use with `rewrite [add_zero]`.
  * `add_succ (a b : ℕ) : a + succ(b) = succ(a + b)`. Use with `rewrite [add_succ]`.
  * The principle of mathematical induction. Use with `induction_on` (see below)
  

## Spells:

  * `rfl` :  proves goals of the form `X = X`
  * `rewrite [h]` : if h is a proof of `A = B`, changes all A's in the goal to B's.
  * `induction_on n with d hd` : we're going to learn this right now.

# Important thing: 

This is a *really* good time to check you understand about the spell book and the inventory on
the left. Eveything you need is collected in those lists. They 
will prove invaluable as the number of theorems we prove gets bigger. On the other hand,
we only need to learn one more spell to really start going places, so let's learn about
that spell right now.

OK so let's see induction in action. We're going to prove

  `zero_add (n : ℕ) : 0 + n = n`. 

That is: for all natural numbers $n$, $0+n=n$. Wait $-$ what is going on here?
Didn't we already prove that adding zero to $n$ gave us $n$?
No we didn't! We proved $n + 0 = n$, and that proof was called `add_zero`. We're now
trying to establish `zero_add`, the proof that $0 + n = n$. But aren't these two theorems
the same? No they're not! It is *true* that `x + y = y + x`, but we haven't
*proved* it yet, and in fact we will need both `add_zero` and `zero_add` in order
to prove this. In fact `x + y = y + x` is the boss level for addition world,
and `induction_on` is the only other spell you'll need to beat it.

Now `add_zero` is one of Peano's axioms, so we don't need to prove it, we already have it
(indeed, if you've opened the Addition World theorem statements on the left, you can even see it).
To prove `0 + n = n` we need to use induction on $n$. While we're here,
note that `zero_add` is about zero add something, and `add_zero` is about something add zero.
The names of the proofs tell you what the theorems are. Anyway, let's prove `0 + n = n`.

Start by casting `induction_on n`.
"

Statement (n : ℕ) : 0 + n = n := by
  sorry
  -- induction_on n
  -- rewrite [add_zero]
  -- rfl
  -- rewrite [add_succ]
  -- rewrite [ind_hyp]
  -- rfl

Message : (0 : ℕ) + 0 = 0  => "
We now have *two goals!* The
induction spell has generated for us a base case with `n = 0` (the goal at the top)
and an inductive step (the goal underneath). The golden rule: **spells operate on the current goal** --
the goal at the top. So let's just worry about that top goal now, the base case `0 + 0 = 0`.

Remember that `add_zero` (the proof we have already) is the proof of `x + 0 = x`
(for any $x$) so we can try

`rewrite [add_zero]`

What do you think the goal will change to? Remember to just keep
focussing on the top goal, ignore the other one for now, it's not changing
and we're not working on it.
"

Message (n : ℕ) (ind_hyp: 0 + n = n) : 0 + succ n = succ n => 
"
Great! You solved the base case. We are now be back down
to one goal -- the inductive step. 

We have a fixed natural number `n`, and the inductive hypothesis `ind_hyp : 0 + n = n`
saying that we have a proof of `0 + n = n`.  
Our goal is to prove `0 + succ n = succ n`. In words, we're showing that
if the lemma is true for `n`, then it's also true for the number after `n`.
That's the inductive step. Once we've proved this inductive step, we will have proved
`zero_add` by the principle of mathematical induction.

To prove our goal, we need to use `add_succ`. We know that `add_succ 0 n`
is the result that `0 + succ n = succ (0 + n)`, so the first thing
we need to do is to replace the left hand side `0 + succ n` of our
goal with the right hand side. We do this with the `rewrite` spell. You can write

`rewrite [add_succ]`

(or even `rewrite [add_succ 0 n]` if you want to give Lean all the inputs instead of making it
figure them out itself).
"

Message (n : ℕ) (ind_hyp: 0 + n = n) : succ (0 + n) = succ n => 
"Well-done! We're almost there. It's time to use our induction hypothesis.
Cast

`rewrite [ind_hyp]`

and finish by yourself.
"

Conclusion "Congratulations for completing your first inductive proof!"

Tactics rfl rewrite induction_on

Lemmas add_succ add_zero