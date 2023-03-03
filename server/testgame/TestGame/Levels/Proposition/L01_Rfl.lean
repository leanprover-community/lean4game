import TestGame.Metadata

Game "TestGame"
World "Proposition"
Level 2

Title "Aller Anfang ist... ein Einzeiler?"

Introduction
"
Jetzt gehen wir aber einen Schritt zurück und lernen, wie man konkret mit Lean arbeitet,
damit du verstehst, was `tauto` hinter der Kulisse macht.

Eine der grundlegendsten Taktiken ist `rfl` (für \"reflexivity\"), welche dazu da ist,
ein Goal der Form $X = X$ zu schließen.
"

Statement
"Zeige $ 42 = 42 $." : 42 = 42 := by
  rfl

-- Hint : 42 = 42 =>
-- "Die Taktik `rfl` beweist ein Goal der Form `X = X`."

HiddenHint : 42 = 42 =>
"Die beiden Seiten dieser Gleichung sind identisch, also gib `rfl` ein und drücke Enter ⏎"

Conclusion "Bravo! PS: `rfl` steht für \"reflexivity\"."

NewTactics rfl
DisabledTactics tauto
