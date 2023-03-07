import TestGame.Metadata

Game "TestGame"
World "Proposition"
Level 6

Title "Not"

Introduction
"
Der Schelm hat noch eine Schwester dabei.
"

Statement "" :
  ¬False := by
  trivial

Hint : ¬False => "
  **Robo** Dieses Zeichen `¬` bedeutet Negation. Also wenn eine Aussage `(A : Prop)`
  wahr ist, dann ist  `¬A` falsch, und umgekehrt.

  **Du** Und `False` ist wahrscheinlich die Aussage, die immer falsch ist?

  **Robo** Ja, richtig.

  **Du** Ist das jetzt nicht doch wieder trivial?

  **Robo** Probier mal!
"

Conclusion
"
Die Schwester lacht und eilt ihrem Bruder hinterher.
"

NewTactics trivial
DisabledTactics tauto
