import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

--set_option tactic.hygienic false

--set_option autoImplicit false


Game "TestGame"
World "Proposition"
Level 12

Title "Oder"

Introduction
"
Wenn man hingegen ein ODER `(h : A ∨ B)` in den Annahmen hat, kann man dieses
ähnlich wie beim UND mit `rcases h` aufteilen.

**Wichtig:** der Syntax dafür ist `rcases h with h | h`. Das \"`h | h`\" bedeutet, dass
wir in beiden Fälle (linke oder rechte Seite wahr) diese Seite wieder `h` nennen wollen.

Der Unterschied ist, dass man beim UND eine Annahme in zwei Einzelteile zerlegt (mit `⟨h₁, h₂⟩`).
Beim ODER hingegen, kriegt man stattdessen zwei *Goals*, nämlich eines wo man annimmt,
die linke Seite sei wahr und eines wo man annimmt, rechts sei wahr.

*Notiz:* UND hat stärkere Bindung als ODER, und beide binden rechts, d.h.
`A ∨ B ∧ C` wird als `A ∨ (B ∧ C)` gelesen. Zudem binden beide nach rechts,
also `A ∨ B ∨ C` ist `A ∨ (B ∨ C)`.
"

Statement
"Angenommen \"$A$ oder ($A$ und $B$)\" wahr ist, zeige, dass $A$ wahr ist."
    (A B : Prop) (h : A ∨ (A ∧ B)) : A := by
  rcases h with h | h
  assumption
  rcases h with ⟨h₁, h₂⟩
  assumption

Hint (A : Prop) (B : Prop) (h : A ∨ (A ∧ B)) : A =>
"Als erstes kannst du das ODER in den Annahmen mit `rcases h with h | h` zerlegen."

Message (A : Prop) (B : Prop) (h : A ∧ B) : A =>
"Jetzt noch das UND in den Annahmen mit `rcases h with ⟨h₁, h₂⟩` zerlegen."

Tactics assumption rcases
