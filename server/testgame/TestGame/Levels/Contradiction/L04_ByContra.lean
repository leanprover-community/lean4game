import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring
import Mathlib

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 4

Title "Per Widerspruch"

Introduction
"
Als Übung zu `by_contra` und dem bisher gelernten, zeige folgendes Lemma welches
wir für die Kontraposition brauchen werden:
"

Statement not_imp_not
"$A \\Rightarrow B$ ist äquivalent zu $\\neg B \\Rightarrow \\neg A$."
    (A B : Prop) : A → B ↔ (¬ B → ¬ A) := by
  constructor
  intro h b
  by_contra a
  suffices b : B
  contradiction
  apply h
  assumption
  intro h a
  by_contra b
  suffices g : ¬ A
  contradiction
  apply h
  assumption

-- TODO: Forbidden Tactics: apply, rw
-- TODO: forbidden Lemma: not_not

Hint (A : Prop) (B : Prop) : A → B ↔ (¬ B → ¬ A) =>
""


Conclusion ""

Tactics contradiction constructor intro by_contra sufficesₓ haveₓ apply assumption
