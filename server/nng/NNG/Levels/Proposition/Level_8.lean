import NNG.Metadata
import NNG.MyNat.Addition
import NNG.MyNat.Theorems.Proposition


Game "NNG"
World "Proposition"
Level 8
Title "(P → Q) → (¬ Q → ¬ P)"

open MyNat

Introduction
"
There is a false proposition `false`, with no proof. It is
easy to check that $\\lnot Q$ is equivalent to $Q\\implies {\tt false}$,
and in the natural number game we call this

`not_iff_imp_false (P : Prop) : ¬ P ↔ (P → false)`

So you can start the proof of the contrapositive below with

`repeat {rw not_iff_imp_false},`

to get rid of the two occurences of `¬`, and I'm sure you can
take it from there (note that we just added `not_iff_imp_false` to the
theorem statements in the menu on the left). At some point your goal might be to prove `false`.
At that point I guess you must be proving something by contradiction.
Or are you? 
"

Statement
"If $P$ and $Q$ are propositions, and $P\\implies Q$, then
$\\lnot Q\\implies \\lnot P$. "
    (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  rw [not_iff_imp_false]
  rw [not_iff_imp_false]
  intro f
  intro h
  intro p
  apply h
  apply f
  exact p

NewLemma not_iff_imp_false

Conclusion
"

"
