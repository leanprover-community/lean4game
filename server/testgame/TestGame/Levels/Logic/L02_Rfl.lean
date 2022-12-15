import TestGame.Metadata

Game "TestGame"
World "Logic"
Level 2

Title "Definitionally equal"

Introduction
"
**Vorsicht:** `rfl` kann auch Gleichungen beweisen, wenn die beiden Terme Lean-intern gleich
definiert sind, auch wenn diese unterschiedlich dargestellt werden. Das kann anfänglich
zu Verwirrung führen.

So sind `2` definiert als `1 + 1`, deshalb funktioniert `rfl` auch hier.
"

Statement "Zeige dass $1 + 1$ zwei ist." : 1 + 1 = 2 := by
  rfl

Conclusion
"
**Notiz:** Die meisten anderen Taktiken versuchen am Schluss automatisch `rfl`
aufzurufen, deshalb brauchst du das nur noch selten.
"

Tactics rfl
