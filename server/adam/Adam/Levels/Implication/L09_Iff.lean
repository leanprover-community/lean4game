import Adam.Metadata
import Std.Tactic.RCases
import Adam.Options.MathlibPart

Game "Adam"
World "Implication"
Level 9

Title "Genau dann wenn"

Introduction
"
**Operationsleiter**:  Ah, die nächste Seite ist auch von diesem Kollegen. Aber da ist noch eine Notiz bei.  Wir hatten hierfür schon einmal einen Beweis, aber den mochte er nicht.  Er wollte einen Beweis, der weder `rw` noch `apply` verwendet!!

Er holt tief Luft und seuft.

**Operationsleiter**:  Ich glaube, der stellt sich immer viel dümmer, als er ist.  Aber meint Ihr, Ihr schafft das?
"

Statement (A B : Prop) : (A ↔ B) → (A → B) := by
  Hint "**Du**: Hmm, mindestens mit der Implikation kann ich anfangen."
  Hint (hidden := true) "**Robo**: Genau, das war `intro`."
  intro h
  Hint "**Du**: Also, ich kenne `rw [h]` und `apply h.mp`, aber das wollten wir ja diesmal vermeiden.

  **Robo**: Was du machen könntest, ist, mit `rcases h with ⟨mp, mpr⟩` die Annahme in zwei
  Teile aufteilen."
  Branch
    intro a
    Hint "**Robo**: Hier müsstest du jetzt `rw [←h]` oder `apply h.mp` benutzen.
    Geh lieber einen Schritt zurück, sodass das Goal `A → B` ist."
  rcases h with ⟨mp, mpr⟩
  Hint (hidden := true) "**Du**: Ah, und jetzt ist das Beweisziel in den Annahmen."
  assumption

Conclusion
"
**Operationsleiter**: Perfekt, das sollte reichen!
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
