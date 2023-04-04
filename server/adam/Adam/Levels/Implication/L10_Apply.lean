import Adam.Metadata
import Adam.Options.MathlibPart


Game "Adam"
World "Implication"
Level 10

Title "Lemmas"

Introduction
"
Beim nächsten Problem stutzt der Operationsleiter.

**Operationsleiter**:  Ehrlich gesagt weiß ich gar nicht, wo dieses Blatt herkommt.  Das ist gar nicht von mir.  Sieht aber irgendwie interessant aus.
"

Statement (A : Prop) : ¬A ∨ A := by
  Hint "**Du**: Das scheint wieder ziemlich offensichtlich.

  **Robo**:  Nee, offensichtlich ist das nicht.  Aber ich glaube, es gibt ein wohlbekanntens Lemma, das hier weiterhilft:
  `not_or_of_imp` besagt `(A → B) → ¬ A ∨ B`.  Da die rechte Seite der Implikation mit deinem Beweisziel übereinstimmt,
  kannst du es mit `apply not_or_of_imp` anwenden.

  **Du**:  `Wohlbekannt` auf Implis?

  **Robo**:  Werden wir sehen. Probiers aus!"
  Branch
    right
    Hint "**Du**: Und jetzt?

    **Robo**: `right/left` funktioniert hier nicht, da du nicht weißt, ob `A` wahr oder falsch ist."
  Branch
    left
    Hint "**Du**: Und jetzt?

    **Robo**: `right/left` funktioniert hier nicht, da du nicht weißt, ob `A` wahr oder falsch ist."
  apply not_or_of_imp
  Hint (hidden := true) "**Robo**: Ich würde wieder mit `intro` weitermachen."
  intro
  assumption

Conclusion
"
Der Operationsleiter nickt zustimmend.  Offenbar war ihm `not_or_of_imp` tatsächlich bekannt.
"

LemmaTab "Logic"
NewLemma not_or_of_imp
DisabledTactic tauto
