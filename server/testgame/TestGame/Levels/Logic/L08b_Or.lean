import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

--set_option tactic.hygienic false

--set_option autoImplicit false


Game "TestGame"
World "Logic"
Level 16

Title "Oder - Bonus"

Introduction
"
Wenn man hingegen ein ODER `(h : A ∨ B)` in den Annahmen hat, kann man dieses
ähnlich wie beim UND mit `rcases h` aufteilen.

**Wichtig:** der Syntax dafür ist `rcases h with h₁ | h₂`.

Der Unterschied ist, dass man beim UND eine Annahme in zwei Einzelteile zerlegt (mit $⟨h₁, h₂⟩$).
Beim ODER hingegen, kriegt man stattdessen zwei *Goals*, nämlich eines wo man annimmt,
die linke Seite sei wahr und eines wo man annimmt, rechts sei wahr.
"

Statement distributivity
    "Angenommen $ A \\lor (B \\land C)$ is wahr, zeige, dass $(A \\lor B) \\land (A \\lor C)$."
    (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  rcases h with ha | h
  constructor
  left
  assumption
  left
  assumption
  rcases h with ⟨h₁, h₂⟩
  constructor
  right
  assumption
  right
  assumption

Message (A : Prop) (B : Prop) (C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) =>
"Als erstes solltest du das OR in der Annahme `(h: A ∨ (B ∧ C))` aufteilen:"

Hint (A : Prop) (B : Prop) (C : Prop) (h : A) : (A ∨ B) ∧ (A ∨ C) =>
"Wie wär's mit zerlegen?"

Hint (A : Prop) (B : Prop) : (A ∨ B) =>
"`left` oder `right`?"

Message (A : Prop) (B : Prop) (C : Prop) (h : (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) =>
"Und jetzt der Fall, falls die rechte Seite $B \\land C$ wahr ist. Zerlege diese
Annahme doch als erstes."

Message (A : Prop) (B : Prop) (C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) =>
"Jetzt musst du die Annahme $A \\lor (B \\land C)$ trotzdem noch mit `rcases` zerlegen."

Message (A : Prop) (B : Prop) (C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ C) =>
"So musst du die Annahme $A \\lor (B \\land C)$ nochmals mit `rcases` zerlegen...

Wenn du am Anfang zuerst `rcases` und dann `constructor` aufrufst,
musst du das hier nur einmal machen..."

Message (A : Prop) (B : Prop) (C : Prop) (h : B ∧ C) : A ∨ B =>
"Die Annahme `B ∧ C` kannst du auch mit `rcases` zerlegen."

Message (A : Prop) (B : Prop) (C : Prop) (h : B ∧ C) : A ∨ C =>
"Die Annahme `B ∧ C` kannst du auch mit `rcases` zerlegen."

Message (A : Prop) (B : Prop) (C : Prop) (h : B ∧ C) : C =>
"Die Annahme `B ∧ C` kannst du auch mit `rcases` zerlegen."


-- Statement umsortieren
--     "Angenommen $(A \\land B) \\lor (D \\lor C)$ is wahr, zeige, dass "
--     (A B C D : Prop) (h : (A ∧ B) ∨ (D ∨ C)) : (A ∧ B) ∨ (C ∨ D) := by
--   rcases h with x | (h | h)
--   left
--   assumption
--   right
--   right
--   assumption
--   right
--   left
--   assumption

-- Message (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h : (A ∧ B) ∨ (D ∨ C)) : (A ∧ B) ∨ (C ∨ D) =>
-- "Man kann hier entweder in mehren Schritten `rcases` anwenden:
-- ```
--   rcases h with h₁ | h₂
--   rcases h₁ with ⟨hA, hB⟩
--   [...]
--   rcases h₂ with h | h
-- ```
-- oder man kann dies in einem Schritt verschachteln:
-- ```
-- rcases h with ⟨ha, hb⟩ | (h | h)
-- ```
-- "

Tactics left right assumption constructor rcases apply
