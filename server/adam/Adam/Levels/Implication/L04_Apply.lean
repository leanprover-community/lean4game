import Adam.Metadata

set_option tactic.hygienic false

Game "Adam"
World "Implication"
Level 4

Title "Implikation"

Introduction
"
**Operationsleiter**:  Das hier ist jetzt weider ein lokales Problem.
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

Conclusion "**Operationsleiter**:  Ihr seid echt super!"

DisabledTactic tauto
