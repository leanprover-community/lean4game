import Adam.Metadata

import Adam.ToBePorted

Game "Adam"
World "Contradiction"
Level 2

Title "Es reicht!"

Introduction
"
**Benedictus**:  Ihr hättet natürlich auch erst das Hauptresultat und dann das Zwischenresultat beweisen können.  Das könnt Ihr ja mal an dieser Aufgabe probieren, die ist ganz ähnlich.
"

-- Die Taktik `suffices` funktioniert genau gleich wie `have`,
-- vertauscht aber die beiden Beweisblöcke:

-- ```
-- suffices h : [Aussage]
-- [Beweis des Goals (mithilfe von h)]
-- [Beweis der Aussage h]
-- ```
-- Auf Deutsch entspricht `suffices g : [Aussage]` dem Ausdruck
-- \"Es genügt zu zeigen, dass `[Aussage]` wahr ist.\"

-- Man kann `have` und `suffices` nach belieben vertauschen. Bevorzugt, wählt man es so,
-- dass der erste Beweisblock der kürzere ist. Zum Beispiel wäre bei der vorigen Aufgabe
-- `suffices` schöner gewesen:

--   "Angenommen, man hat eine Implikation $A \\Rightarrow \\neg B$ und weiss, dass
--    $A \\land B$ wahr ist. Zeige, dass dies zu einem Widerspruch führt."

Statement
    (A B : Prop) (h : A → ¬ B) (k₁ : A) (k₂ : B) : False := by
  Hint "**Robo**: Ich weiss was er meint! Anstatt `have` kannst du auch `suffices`
  verwenden. Das funktioniert genau gleich, außer, dass dann die beiden Beweisziele vertauscht sind.

  **Du**: Also nach `suffices g : ¬B` muss ich dann zuerst zeigen, wie man mit `g` den Beweis
  abschliesst, bevor ich `g` beweise?

  **Robo**: Genau!"
  suffices g : ¬ B
  Hint "**Robo**: Also hier beendest du den Beweis unter der Annahme `{g}` sei wahr."
  contradiction
  Hint "**Robo**: Und hier beweist du das Zwischenresultat."
  apply h
  assumption

NewTactic «suffices»
DisabledTactic «have»

Conclusion "**Benedictus**:  Genau so meinte ich das.  Ob Ihr nun in Zukunft  `have` und `suffices` verwendet, ist reine Geschmacksfrage.  Hauptsache, Ihr wisst, wie Ihr entfernte Ziele in kleinen Schritte erreicht."
