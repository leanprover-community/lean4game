import NNG.Metadata
import NNG.MyNat.AdvAddition
import NNG.Levels.Addition

Game "NNG"
World "AdvAddition"
Level 1
Title "`succ_inj`. A function."

open MyNat

Introduction
"
Let's finally learn how to use `succ_inj`:

```
succ_inj (a b : ℕ) :
  succ a = succ b → a = b
```
"

Statement -- MyNat.succ_inj'
"For all naturals $a$ and $b$, if we assume $\\operatorname{succ}(a)=\\operatorname{succ}(b)$,
then we can deduce $a=b$."
    {a b : ℕ} (hs : succ a = succ b) :  a = b := by
  Hint "You should know a couple
  of ways to prove the below -- one directly using an `exact`,
  and one which uses an `apply` first. But either way you'll need to use `succ_inj`."
  Branch
    apply succ_inj
    exact hs
  exact succ_inj hs

NewLemma MyNat.succ_inj
LemmaTab "Nat"

Conclusion
"
**Important thing**:

You can rewrite proofs of *equalities*. If `h : A = B` then `rw [h]` changes `A`s to `B`s.
But you *cannot rewrite proofs of implications*. `rw [succ_inj]` will *never work*
because `succ_inj` isn't of the form $A = B$, it's of the form $A\\implies B$. This is one
of the most common mistakes I see from beginners. $\\implies$ and $=$ are *two different things*
and you need to be clear about which one you are using.
"
