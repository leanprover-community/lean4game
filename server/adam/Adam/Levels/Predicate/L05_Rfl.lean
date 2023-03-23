import Adam.Metadata

Game "Adam"
World "Predicate"
Level 5

Title "Definitionally equal"

Introduction
"
Müde ruht ihr euch in eurer Bleibe aus. Du schaust doch eine Lücke in den Blättern vielen
kleinen Vögeln bei der Nahrungssuche zu.

**Du**: Sag mal Robo, ich hab vorhin ein Kind überhört, dass seinem Spielgefährten erklärt hat,
folgendes sei mit `rfl` zu beweisen:
"

Statement : 1 + 1 = 2 := by
  Hint "**Du**: Wieso nicht `ring`?

  **Robo**: Klar, `ring` geht auch und ist intuitiver.
  Für `rfl` kommt es darauf an, wie die Sachen genau definiert sind: `1 + 1` ist als
  `(0.succ).succ` definiert und `2` halt ebenfalls.
  "
  rfl

OnlyTactic rfl

Conclusion
"
**Du**: Dann war das mehr Glück?

**Robo**: Das ist eine Art die Welt zu sehen…

Damit fällst du in einen ruhigen Schlaf.
"
