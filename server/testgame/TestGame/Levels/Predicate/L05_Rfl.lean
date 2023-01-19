import TestGame.Metadata

Game "TestGame"
World "Predicate"
Level 5

Title "Definitionally equal"

Introduction
"
Als kleine Nebenbemerkung:

Auf Grund der Implementation in Lean brauchst du die Taktik `ring` gar nicht, wenn
du Gleichungen über `ℕ` hast, die keine Variablen enthalten:

So ist zum Beispiel `2` als `1 + 1` definiert, deshalb kannst du $1 + 1 = 2$ einfach mit
`rfl` beweisen.
"

Statement
"Zeige dass $1 + 1$ zwei ist." :
    1 + 1 = 2 := by
  rfl

Conclusion
"
**Notiz:** Die meisten anderen Taktiken versuchen am Schluss automatisch `rfl`
aufzurufen, deshalb brauchst du das nur noch selten.
"

Tactics rfl
