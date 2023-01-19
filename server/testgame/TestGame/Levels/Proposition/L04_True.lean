import TestGame.Metadata

Game "TestGame"
World "Proposition"
Level 4

Title "True/False"

Introduction
"
Unter den logischen Aussagen gibt es zwei spezielle Aussagen:

- `True` ist eine Aussage, die immer und bedingungslos wahr ist.
- `False` ist eine Aussage, die nie wahr ist.

Die Aussage `True` werden wir kaum brauchen, die Aussage `False` ist jedoch wichtig, sie
repräsentiert einen Widerspruch. Mehr dazu in den nächsten Levels.

**Beachte**, dass beide gross geschrieben werden. In Lean gibt es auf das klein geschriebene
`true` und `false`, diese sind aber etwas anderes (Typ `Bool` und nicht `Prop`)
und werden erst mal nicht gebraucht.

Wir können `True` aus dem nichts mit der Taktik `trivial` beweisen.

*Bemerkung: Was die Taktik `trivial` kann und nicht kann bleibt in diesem Spiel ein bisschen eine Blackbox,
aber manchmal ist sie nützlich.*
"

Statement
"Zeige, dass die logische Aussage `True` immer wahr ist." :
True := by
  trivial

Conclusion ""

Tactics trivial
