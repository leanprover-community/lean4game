import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Implication"
Level 4

Title "Implikation"

Introduction
"
**Du** *(zu Robo)*: Testen die uns eigentlich hier?

Ein älteres Gruppenmitglied schiebt ein Tablet über den Tisch und beginnt in leiser
Stimme zu erklären.

**Mitarbeiterin**: Eines unserer Kontrollelemente ist kaputt und ist verwirrt, wo Sachen hinkommen.
Gesteuert werden diese über Panels, und hier hab ich das Übungspanel, mit dem wir neue
Ingeneure ausbilden:
"

Statement (A B C : Prop) (f : A → B) (g : B → C) : A → C := by
  Hint "**Du**: Ich soll Implikationen $A \\Rightarrow B \\Rightarrow C$ zu $A \\Rightarrow C$
  kombinieren?

  **Robo**: Am besten fängst du mit `intro` an und arbeitest dich dann rückwärts durch."
  intro hA
  Hint (hidden := true) "**Robo**: Das ist wieder eine Anwendung von `apply`."
  apply g
  apply f
  assumption

Conclusion "**Du**: Ich hab das Konzept verstanden.

Die Mitarbeiterin ist zufrieden und wünscht euch Glück auf der Mission."

DisabledTactic tauto
