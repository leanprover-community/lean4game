import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvProposition"
Level 10
Title "The law of the excluded middle."

open MyNat

Introduction
"
We proved earlier that `(P → Q) → (¬ Q → ¬ P)`. The converse,
that `(¬ Q → ¬ P) → (P → Q)` is certainly true, but trying to prove
it using what we've learnt so far is impossible (because it is not provable in
constructive logic).

"

Statement
"If $P$ and $Q$ are true/false statements, then
$$(\\lnot Q\\implies \\lnot P)\\implies(P\\implies Q).$$ 
"
    (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by
  Hint "For example, you could start as always with

  ```
  intro h p
  ```
  "
  intro h p
  Hint "From here there is no way to continue with the tactics you've learned so far.

  Instead you can call `by_cases q : Q`. This creates **two goals**, once under the assumption
  that `Q` is true, once assuming `Q` is false."
  by_cases q : Q
  Hint "This first case is trivial."
  exact q
  Hint "The second case needs a bit more work, but you can get there with the tactics you've already
  learned beforehand!"
  have j := h q
  exfalso
  apply j
  exact p

NewTactic by_cases

Conclusion
"
This approach assumed that `P ∨ ¬ P` is true, which is called \"law of excluded middle\".
It cannot be proven using just tactics like `intro` or `apply`.
`by_cases p : P` just does `rcases` on this result `P ∨ ¬ P`.


OK that's enough logic -- now perhaps it's time to go on to Advanced Addition World!
Get to it via the main menu.
"

-- TODO: I cannot really import `tauto` because of the notation `ℕ` that's used
-- for `MyNat`.
-- ## Pro tip

-- In fact the tactic `tauto` just kills this goal (and many other logic goals) immediately. You'll be
-- able to use it from now on.

