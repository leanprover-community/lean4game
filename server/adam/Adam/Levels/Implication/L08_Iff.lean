import Adam.Metadata

set_option tactic.hygienic false

Game "Adam"
World "Implication"
Level 8

Title "Genau dann wenn"

Introduction
"
Der Koch kommt erfreut hinter einem grossen Topf hervor.

**Koch**: Sagt mal, gestern hat mir jemand was erzählt und es will einfach nicht aus
meinem Kopf…
"

Statement (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  Hint "**Du**: Naja ich kann wohl immerhin mal mit `intro` anfangen und annehmen,
  dass `{A}` wahr sei…

  **Robo**: und dann schauen wir weiter!"
  intro hA
  Hint "**Robo**: Also eine Implikation wendet man mit apply an…

  **Du**: Weiss ich ja!"
  apply g
  Hint "**Robo**: …und du kannst die Implikation `{A} → {B}` genau gleich mit
  `apply {h}.mp` anwenden.

  **Du**: Aber ich könnte hier auch `rw [← h]` sagen, oder?

  **Robo**: Klar, aber offenbar versteht der Koch das `rw` nicht.
  "
  apply h.mp
  assumption

Conclusion "**Koch**: Danke vielmals! Jetzt muss ich aber schauen dass die Suppe nicht verkocht!

Und er eilt davon."

NewTactic apply assumption
DisabledTactic tauto rw
