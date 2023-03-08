import TestGame.Metadata

import Init.Data.ToString
-- #check List UInt8

Game "TestGame"
World "Implication"
Level 7

Title "Genau dann wenn"

Introduction
"
Hat man ein `(h : A ↔ B)` in den Annahmen, hat man die gleichen beiden Optionen wie beim
logischen UND plus noch eine neue:

1. Mit `h.mp` und `h.mpr` (oder `h.1` und `h.2`) kann man die einzelnen Implikationen
   direkt auswählen.
2. Mit `rcases h with ⟨h₁, h₂⟩` könnte man die Struktur `h` zerlegen und man erhält zwei
   separate Annahmen `(h₁ : A → B)` und `(h₂ : B → A)`
3. **Mit** `rw [h]` **kann man im Goal `A` durch `B` ersetzen.**

Wir widmen uns zuerst `rw`. Dies steht für \"rewrite\". Da $A$ und $B$ logisch äquivalent
sind, kann man beliebig das eine mit dem anderen vertauschen.
`rw [h]` ersetzt $A$ durch $B$.
Dabei gibt es noch einige Tricks:

- `rw [← h]` ersetzt umgekehrt $B$ durch $A$ (`\\l`, kleines L).
- `rw [h, g]` ist das gleiche wie `rw [h]` gefolgt von `rw [g]`.
"

Statement
    "Zeige dass `B ↔ C`."
    (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  rw [h₁]
  rw [←h₂]
  assumption

HiddenHint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C =>
"Im Goal kommt `C` vor und `h₁` sagt `C ↔ D`.
Probiers doch mit `rw [h₁]`."

HiddenHint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : A ↔ C =>
"Im Goal kommt `C` vor und `h₁` sagt `C ↔ D`.
Probiers doch mit `rw [h₁]`."

Hint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ D =>
"Man kann auch rückwärts umschreiben:
`rw [←h₂]` ersetzt man im Goal `B` durch `a` (`\\l`, also ein kleines L)"

HiddenHint (A : Prop) (B : Prop) (h : A ↔ B) : A ↔ B =>
"Schau mal durch die Annahmen durch."


-- These should not be necessary if they don't use `rw [] at`.
HiddenHint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ C) : B ↔ C =>
"Auch eine Möglichkeit... Kannst du das Goal so umschreiben,
dass es mit einer Annahme übereinstimmt?"

HiddenHint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : B ↔ D) : B ↔ C =>
"Auch eine Möglichkeit.. Kannst du das Goal so umschreiben, dass es mit einer Annahme übereinstimmt?"

Hint (A : Prop) (B : Prop) (h : B ↔ A) : A ↔ B =>
"Naja auch Umwege führen ans Ziel... Wenn du das Goal zu `A ↔ A` umschreibst, kann man es mit
`rfl` beweisen (rsp. das passiert automatisch.)"

Hint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h₁ : C ↔ D) (h₂ : D ↔ B) (h₃ : D ↔ A) : B ↔ C =>
"Das ist nicht der optimale Weg..."

Hint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h₁ : C ↔ D) (h₂ : D ↔ B) (h₃ : A ↔ D) : B ↔ C =>
"Das ist nicht der optimale Weg..."


NewTactic rw assumption
