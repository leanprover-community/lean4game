import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Cases

Game "TestGame"
World "Implication"
Level 9

Title "Genau dann wenn"

Introduction
"
Noch während der Koch wieder zu seiner Suppe geht, kommt sein erster Gehilfe hervor.

**Gehilfe**: Ich hab gestern noch was anderes gehört, könnt ihr mir da auch helfen?
Aber ich versteh nicht ganz was ihr meinem Chef erklärt habt.
"

Statement (A B : Prop) : (A ↔ B) → (A → B) := by
  Hint "**Du**: Hmm, mindestens mit der Implikation kann ich anfangen."
  Hint (hidden := true) "**Robo**: Genau, das war `intro`."
  intro h
  Hint "**Du**: Also ich kenn `rw [h]` und `apply h.mp`, aber das will er wohl nicht hören.

  **Robo**: Was du machen könntest ist mit `rcases h with ⟨mp, mpr⟩` die Annahme in zwei
  Teile aufteilen."
  Branch
    intro a
    Hint "**Robo**: Hier müsstest du jetzt `rw [←h]` oder `apply h.mp` benützen, aber der
    Gehilfe will, dass du zwingend eine dritte Variante benützt. Geh doch einen
    Schritt zurück so dass das Goal `A → B` ist."
  rcases h with ⟨mp, mpr⟩
  Hint (hidden := true) "**Du**: Ah und jetzt ist das Resultat in den Annahmen."
  assumption

Conclusion
"
**Gehilfe**: Ah danke! Und jetzt versteh ich auch die Zusammenhänge!
"
OnlyTactic intro rcases assumption
DisabledTactic rw apply tauto

-- -- TODO: The new `cases` works differntly. There is also `cases'`
-- example (A B : Prop) : (A ↔ B) → (A → B) := by
--   intro h
--   cases h with
--   | intro a b =>
--     assumption

-- example (A B : Prop) : (A ↔ B) → (A → B) := by
--   intro h
--   cases' h with a b
--   assumption
