import Adam.Metadata

set_option tactic.hygienic false

Game "Adam"
World "Implication"
Level 8

Title "Genau dann wenn"

Introduction
"
  **Operationsleiter**: Das hier ist wieder für meinen beschränkten Kollegen.  Ich glaube, `rw` mag der auch nicht.  Geht das trotzdem?
"

Statement (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  Hint "**Du**: Naja ich kann wohl immerhin mal mit `intro` anfangen und annehmen,
  dass `{A}` wahr sei …

  **Robo**: … und dann schauen wir weiter!"
  intro hA
  Hint "**Robo**: Also eine Implikation wendet man mit `apply` an …

  **Du**: Weiß ich doch!"
  apply g
  Hint "**Robo**: … und Du kannst die Implikation `{A} → {B}` genau gleich mit
  `apply {h}.mp` anwenden.

  **Du**: Aber normalerweise könnte ich hier auch `rw [← h]` sagen, oder?

  **Robo**: Ja ja, nur nicht auf der anderen Seite des Mondes.
  "
  apply h.mp
  assumption

Conclusion "**Operationsleiter**:  Ok, super.  Das müsste passen.

Er telefoniert wieder.

**Operationsleiter**: Bingo!
"

NewTactic apply assumption
DisabledTactic tauto rw
