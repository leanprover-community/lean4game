import TestGame.Metadata

Game "TestGame"
World "Proposition"
Level 6

Title "Not"

Introduction
"
Wenn eine Aussage `(A : Prop)` wahr oder falsch ist, dann ist die Umkehrung \"nicht $A$\",
geschrieben `¬A` (`\\not`), gegenteilig falsch oder wahr.

Da die Aussage `False` nie wahr ist, ist die Aussage `¬False` immer wahr, genau wie `True`.
"

Statement
"Zeige dass die Aussage `¬False` immer wahr ist." :
    ¬False := by
  trivial

Conclusion ""

NewTactics trivial
DisabledTactics tauto
