import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Addition"
Level 1
Title "the induction tactic."

open MyNat

Introduction
"
OK so let's see induction in action. We're going to prove

```
zero_add (n : ℕ) : 0 + n = n
```

Wait… what is going on here? Didn't we already prove that adding zero to $n$ gave us $n$?

No we didn't! We proved $n + 0 = n$, and that proof was called `add_zero`. We're now
trying to establish `zero_add`, the proof that $0 + n = n$.

But aren't these two theorems the same?

No they're not! It is *true* that `x + y = y + x`, but we haven't *proved* it yet,
and in fact we will need both `add_zero` and `zero_add` in order
to prove this. In fact `x + y = y + x` is the boss level for addition world,
and `induction` is the only other tactic you'll need to beat it.

Now `add_zero` is one of Peano's axioms, so we don't need to prove it, we already have it.
To prove `0 + n = n` we need to use induction on $n$. While we're here,
note that `zero_add` is about zero add something, and `add_zero` is about something add zero.
The names of the proofs tell you what the theorems are. Anyway, let's prove `0 + n = n`.
"

Statement MyNat.zero_add
"For all natural numbers $n$, we have $0 + n = n$."
    (n : ℕ) : 0 + n = n := by
  Hint "You can start a proof by induction over `n` by typing:
  `induction n with d hd`.

  If you use the `with` part, you can name your variable and induction hypothesis, otherwise
  they get default names."
  induction n with n hn
  · Hint "Now you have two goals. Once you proved the first, you will jump to the second one.
    This first goal is the base case $n = 0$.

    Recall that you can use all lemmas that are visible in your inventory."
    Hint (hidden := true) "try using `add_zero`."
    rw [add_zero]
    rfl
  · Hint "Now you jumped to the second goal. Here you have the induction hypothesis
    `{hn} : 0 + {n} = {n}` and you need to prove the statement for `succ {n}`."
    Hint (hidden := true) "look at `add_succ`."
    rw [add_succ]
    Branch
      simp? -- TODO
    Hint (hidden := true) "At this point you see the term `0 + {n}`, so you can use the
    induction hypothesis with `rw [{hn}]`."
    rw [hn]
    rfl

attribute [simp] MyNat.zero_add

NewTactic induction
LemmaTab "Add"

Conclusion
"
## Now venture off on your own.

Those three tactics:

* `induction n with d hd`
* `rw [h]`
* `rfl`

will get you quite a long way through this game. Using only these tactics
you can beat Addition World level 4 (the boss level of Addition World),
all of Multiplication World including the boss level `a * b = b * a`,
and even all of Power World including the fiendish final boss. This route will
give you a good grounding in these three basic tactics; after that, if you
are still interested, there are other worlds to master, where you can learn
more tactics.

But we're getting ahead of ourselves, you still have to beat the rest of Addition World. 
We're going to stop explaining stuff carefully now. If you get stuck or want
to know more about Lean (e.g. how to do much harder maths in Lean),
ask in `#new members` at
[the Lean chat](https://leanprover.zulipchat.com)
(login required, real name preferred). Any of the people there might be able to help.

Good luck! Click on \"Next\" to solve some levels on your own.
"
