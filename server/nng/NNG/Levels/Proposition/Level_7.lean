import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 7
Title "(P → Q) → ((Q → R) → (P → R))"

open MyNat

Introduction
"
If you start with `intro hpq` and then `intro hqr`
the dust will clear a bit and the level will look like this:
```
P Q R : Prop,
hpq : P → Q,
hqr : Q → R
⊢ P → R
```
So this level is really about showing transitivity of $\\implies$,
if you like that sort of language.
"

Statement
"From $P\\implies Q$ and $Q\\implies R$ we can deduce $P\\implies R$."
    (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) := by
  intro hpq hqr
  intro p
  apply hqr
  apply hpq
  exact p

Conclusion
"

"
