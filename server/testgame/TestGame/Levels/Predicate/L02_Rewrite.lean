import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Predicate"
Level 2

Title "Rewrite"

Introduction
"
Robo spuckt den Brief aus, den er dabei hatte, und gibt ihn *Evenine*.

**Evenine**: Das verstehe ich nicht, wisst ihr was damit gemeint ist?

Und sie händigt Dir den Brief:
"

Statement (a b c d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  Hint "**Du**: Schau mal, das ist ja fast genau, was wir auf *Implis* gemacht haben,
  nur jetzt mit Gleichheiten von Zahlen anstatt Genau-Dann-Wenn-Aussagen!

  **Robo**: `=` und `↔` kannst du praktisch gleich behandeln wenns um `rw` geht."
  Hint (hidden := true) "**Du**: Also auch `rw [hₓ]` und `rw [← hₓ]`?

  **Robo**: Probiers doch einfach."
  rw [h₁]
  Hint (hidden := true) "**Du**: Wie war das nochmals mit rückwärts umschreiben?

  **Robo**: `←` ist `\\l`. Und dann `rw [← hₓ]`"
  rw [←h₂]
  assumption

Conclusion
"
**Evenine**: Danke viemals, das hilft uns vermutlich, jetzt Frage ich mich aber…
"

NewTactic assumption rw
