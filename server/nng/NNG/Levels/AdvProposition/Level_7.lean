import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvProposition"
Level 7
Title "`or_symm`"

open MyNat

Introduction
"
Proving that $(P\\lor Q)\\implies(Q\\lor P)$ involves an element of danger.
"

Statement --or_symm
"If $P$ and $Q$ are true/false statements, then
$$P\\lor Q\\implies Q\\lor P.$$ "
    (P Q : Prop) : P ∨ Q → Q ∨ P := by
  Hint "`intro h` is the obvious start."
  intro h
  Branch
    left
    Hint "This is a dead end that is not provable anymore. Hit \"undo\"."
  Branch
    right
    Hint "This is a dead end that is not provable anymore. Hit \"undo\"."
  Hint "But now, even though the goal is an `∨` statement, both `left` and `right` put
  you in a situation with an impossible goal. Fortunately,
  you can do `rcases h with p | q`. (that is a normal vertical slash)
  "
  rcases h with p | q
  Hint " Something new just happened: because
  there are two ways to prove the assumption `P ∨ Q` (namely, proving `P` or proving `Q`),
  the `rcases` tactic turns one goal into two, one for each case.

  So now you proof the goal under the assumption that `P` is true, and waiting under \"Other Goals\"
  there is the same goal but under the assumption that `Q` is true.

  You should be able to make it home from there. "
  right
  exact p
  Hint "Note how now you finished the first goal and jumped to the one, where you assume `Q`."
  left
  exact q

Conclusion
"
Well done! Note that the syntax for `rcases` is different whether it's an \"or\" or an \"and\".

* `rcases h with ⟨p, q⟩` splits an \"and\" in the assumptions into two parts. You get two assumptions
but still only one goal.
* `rcases h with p | q` splits an \"or\" in the assumptions. You get **two goals** which have different
assumptions, once assumping the lefthand-side of the dismantled \"or\"-assumption, once the righthand-side.
"
