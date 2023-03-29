import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Cases
import Mathlib

Game "Adam"
World "Implication"
Level 10

Title "Lemmas"

Introduction
"
Ihr setzt euch hin und der Gehilfe bringt euch allen Suppe. Neben euch sitzt eine Mechanikerin
über ihre Suppe geneigt.

**Mechanikerin**: Sagt mal, ich hab unten über folgendes tiefgründiges Problem nachgedacht:
"

Statement (A : Prop) : ¬A ∨ A := by
  Hint "**Du**: Das scheint ziemlich offensichtlich.

  **Robo**: Ich glaube, sie will eine detailierte Antwort. Ich kenne ein Lemma
  `not_or_of_imp`, was sagt `(A → B) → ¬ A ∨ B`. Da das Resultat des Lemmas mit
  deinem Goal übreinstimmt, kannst du es mit `apply not_or_of_imp` anwenden."
  Branch
    right
    Hint "**Du**: Und jetzt?

    **Robo**: `right/left` funktioniert hier nicht, da du nicht weisst ob `A` wahr oder falsch
    ist."
  Branch
    left
    Hint "**Du**: Und jetzt?

    **Robo**: `right/left` funktioniert hier nicht, da du nicht weisst ob `A` wahr oder falsch
    ist."
  apply not_or_of_imp
  Hint (hidden := true) "**Robo**: Ich würd wieder mit `intro` weitermachen."
  intro
  assumption

Conclusion
"
**Mechanikerin**: Danke vielmals, jetzt bin ich schon viel ruhiger.
"

NewLemma not_or_of_imp
DisabledTactic tauto
