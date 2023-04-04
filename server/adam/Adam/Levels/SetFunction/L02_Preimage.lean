import Adam.Metadata
import Adam.Options.MathlibPart

Game "Adam"
World "SetFunction"
Level 2

Title ""

open Set

Introduction
"
Das Urbild einer Menge `U` unter einer Funktion `f` ist mit `f ⁻¹' U` bezeichnet.

Note: `f ⁻¹` ist das abstrakte, gruppentheoretische Inverse von `f`, was generell nicht existieren muss,
deshalb wurde die andere Notation hier gewählt

"

Statement
    (U : Set ℕ) (f : ℕ → ℕ) : U ⊆ f ⁻¹' (f '' U) := by
  Hint "Fang wieder mal mit `intro` an."
  intro x hx
  Hint "Mit `rw [preimage]` kannst du sehen, wie das Urbild definiert ist."
  rw [preimage]
  Hint "Also musst du jetzt ein Element `y` angeben sodass `f y` in `f '' U` liegt."
  use x
  constructor
  assumption
  rfl

NewDefinition Set.preimage
