import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

--set_option tactic.hygienic false

Game "TestGame"
World "TestWorld"
Level 15

Title "Oder - Bonus"

Introduction
"
Wenn man hingegen ein ODER - `(h : A ∨ B)` - in den Annahmen hat, kann man dieses
ähnlich wie beim UND mit `rcases h` aufteilen.

ABER! Beim UND `(h : A ∧ B)` hat man dann zwei neue Annahmen erhalten, und diese hat man mit
`rcases h with ⟨hA, hB⟩` benannt. Beim ODER `(h : A ∨ B)` kriegt man stattdessen zwei **Goals**
wo man annimmt, dass entweder die linke oder rechte Seite von `h` war ist.
Diese Annahme benennt man dann mit `rcases h with hA | hB`.
"

Statement
    (A B C D : Prop) (h : (A ∧ B) ∨ (D ∨ C)) : (A ∧ B) ∨ (C ∨ D) := by
  rcases h with ⟨ha, hb⟩ | (h | h)
  left
  constructor
  assumption
  assumption
  right
  right
  assumption
  right
  left
  assumption

Message (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h : (A ∧ B) ∨ (D ∨ C)) : (A ∧ B) ∨ (C ∨ D) =>
"Man kann hier entweder in mehren Schritten `rcases` anwenden:
```
  rcases h with h₁ | h₂
  rcases h₁ with ⟨hA, hB⟩
  [...]
  rcases h₂ with h | h
```
oder man kann dies in einem Schritt verschachteln:
```
rcases h with ⟨ha, hb⟩ | (h | h)
```
"

Tactics left right assumption constructor rcases
