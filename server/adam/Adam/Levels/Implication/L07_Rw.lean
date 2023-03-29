import Adam.Metadata

import Init.Data.ToString
-- #check List UInt8

set_option tactic.hygienic false

Game "Adam"
World "Implication"
Level 7

Title "Genau dann wenn"

Introduction
"
Als nächstes begenet ihr jemandem im Flur.

Dieser hat schon von euch gehört und will sofort wissen, ob ihr ihm helfen könnt:
"

Statement (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  Hint "**Du**: $B \\iff A \\iff D \\iff C$, die sind doch alle äquivalent…

  **Robo**: Ja aber du musst ihm helfen umzuschreiben. Mit `rw [h₁]` kannst du `C` durch `D`
  ersetzen."
  rw [h₁]
  Hint "**Du** Und wenn ich in die andere Richtung umschreiben möchte?

  **Robo**: Dann schreibst du ein `←` vor den Namen, also `rw [← hₓ]`."
  Branch
    rw [← h₃]
    Hint "**Du**: Ehm, das ist verkehrt.

    **Robo**: Andersrum wär's besser gewesen, aber wenn du jetzt einfach weitermachst bis du
    sowas wie `A ↔ A` kriegst, kann `rfl` das beweisen.

    **Robo: Da fällt mir ein, `rw` versucht automatisch `rfl` am Ende. Das heisst, du musst
    das nicht einmal mehr schreiben."
    rw [h₂]
  rw [←h₂]
  assumption

Conclusion "Ihr geht weiter und der Operationsleiter zeigt euch die Küche."

NewTactic rw assumption
DisabledTactic tauto
-- NewLemma Iff.symm
