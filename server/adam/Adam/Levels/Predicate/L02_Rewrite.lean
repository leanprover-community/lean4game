import Adam.Metadata
import Mathlib

Game "Adam"
World "Predicate"
Level 2

Title "Rewrite"

Introduction
""

Statement (a b c d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  Hint "**Du**: Schau mal, dieses Problem sieht so ähnlich aus wie eines, das wir auf *Implis* schon gelöst hatten.
  Nur, das hier jetzt Gleichheiten von Zahlen statt Genau-Dann-Wenn-Aussagen stehen!

  **Robo**: Richtig.  Und im Grunde macht das gar keinen Unterscheid.
  Du kannst `=` und `↔` praktisch mit `rw` praktisch gleich behandeln."

  Hint (hidden := true) "**Du**: Also auch `rw [hₓ]` und `rw [← hₓ]`?

  **Robo**: Probiers doch einfach."
  rw [h₁]
  Hint (hidden := true) "**Du**: Wie war das nochmals mit rückwärts umschreiben?

  **Robo**: `←` ist `\\l`. Und dann `rw [← hₓ]`"
  rw [←h₂]
  assumption

Conclusion
""
