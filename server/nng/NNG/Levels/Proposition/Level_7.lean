import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 7
Title "(P → Q) → ((Q → R) → (P → R))"

open MyNat

Introduction ""

Statement
"From $P\\implies Q$ and $Q\\implies R$ we can deduce $P\\implies R$."
    (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) := by
  Hint (hidden := true)"If you start with `intro hpq` and then `intro hqr`
  the dust will clear a bit."
  intro hpq
  Hint (hidden := true) "Now try `intro hqr`."
  intro hqr
  Hint "So this level is really about showing transitivity of $\\implies$,
  if you like that sort of language."
  intro p
  apply hqr
  apply hpq
  exact p

