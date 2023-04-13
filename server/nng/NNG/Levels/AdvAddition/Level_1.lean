import NNG.Metadata
import NNG.MyNat.AdvAddition

Game "NNG"
World "AdvAddition"
Level 1
Title "`succ_inj`. A function."

open MyNat

Introduction
"
Peano's original collection of axioms for the natural numbers contained two further
assumptions, which have not yet been mentioned in the game:

```
succ_inj {a b : mynat} :
  succ(a) = succ(b) → a = b

zero_ne_succ (a : mynat) :
  zero ≠ succ(a)
 ```

The reason they have not been used yet is that they are both implications,
that is,
of the form $P\\implies Q$. This is clear for `succ_inj a b`, which
says that for all $a$ and $b$ we have $succ(a)=succ(b)\\implies a=b$.
For `zero_ne_succ` the trick is that $X\ne Y$ is *defined to mean*
$X = Y\\implies{\\tt false}$. If you have played through Proposition world,
you now have the required Lean skills (i.e., you know the required
tactics) to work with these implications.
Let's finally learn how to use `succ_inj`. You should know a couple
of ways to prove the below -- one directly using an `exact`,
and one which uses an `apply` first. But either way you'll need to use `succ_inj`.
"

Statement -- MyNat.succ_inj'
"For all naturals $a$ and $b$, if we assume $succ(a)=succ(b)$, then we can
deduce $a=b$."
    {a b : ℕ} (hs : succ a = succ b) :  a = b := by
    exact succ_inj hs

NewLemma MyNat.succ_inj MyNat.zero_ne_succ

Conclusion
"
## Important thing.

You can rewrite proofs of *equalities*. If `h : A = B` then `rw h` changes `A`s to `B`s.
But you *cannot rewrite proofs of implications*. `rw succ_inj` will *never work*
because `succ_inj` isn't of the form $A = B$, it's of the form $A\\implies B$. This is one
of the most common mistakes I see from beginners. $\\implies$ and $=$ are *two different things*
and you need to be clear about which one you are using.
"
