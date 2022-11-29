import TestGame.Metadata

Game "TestGame"
World "TestWorld"
Level 2

Title "Definitionally equal"

Introduction
"
Achtung: `rfl` kann auch Gleichungen beweisen, wenn die beiden Terme Lean-intern gleich
definiert sind, auch wenn diese unterschiedlich dargestellt werden.
So sind `1 + 1` und `2` per Definition das Gleiche, da sie beide von Lean als `0.succ.succ`
gelesen werden.

Das kann anfänglich verwirrend sein und das Verhalten hängt von der Lean-Implementation ab.
"

Statement "Zeige dass eins plus eins zwei ist." : 1 + 1 = 2 := by
  rfl

Conclusion
"
Im weiteren führen die meisten anderen Taktiken `refl` automatisch am Ende aus,
deshalb musst du dieses häufig gar nicht mehr schreiben.
"

Tactics rfl
