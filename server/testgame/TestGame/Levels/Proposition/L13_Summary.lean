import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

set_option tactic.hygienic false

Game "TestGame"
World "Proposition"
Level 14

Title "Zusammenfassung"

Introduction
"
Der letzte Untertan tritt vor.  Ihr Anliegen ist etwas komplizierter als die vorherigen.

**Robo** Wirf einfach alles drauf, was Du gelernt hast.  Hier, ich bin sogar so nett und zeig Dir noch einmal die vier wichtigsten Taktiken für diese Situation an.

| (Übersicht) | Und (`∧`)                | Oder (`∨`)              |
|-------------|:-------------------------|:------------------------|
| Annahme     | `rcases h with ⟨h₁, h₂⟩` | `rcases h with h \\| h` |
| Goal        | `constructor`            | `left`/`right`          |
"

-- Note: The other direction would need arguing by cases.

Statement ""
  (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  constructor
  rcases h with h | h
  left
  assumption
  rcases h with ⟨h₁, h₂⟩
  right
  assumption
  rcases h with h | h
  left
  assumption
  rcases h with ⟨h₁, h₂⟩
  right
  assumption

HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : B ∧ C) : (A ∨ B) ∧ (A ∨ C) =>
"**Robo** Das `∧` in der Annahme kannst Du mit `rcases h with ⟨h₁, h₂⟩` zerlegen."

HiddenHint (A : Prop) (B : Prop) (C : Prop) : (A ∨ B) ∧ (A ∨ C) =>
"**Robo** Das `∧` im Goal kannst Du mit `constructor` zerlegen."

HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) =>
"**Robo** Das `∨` in der Annahme kannst Du mit `rcases h with h | h` zerlegen."

HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) =>
"**Robo** Das `∨` in der Annahme kannst Du mit `rcases h with h | h` zerlegen."

HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ C) =>
"**Robo** Das `∨` in der Annahme kannst Du mit `rcases h with h | h` zerlegen."


HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : B ∧ C) : (A ∨ B) =>
"**Robo** Das `∧` in der Annahme kannst Du mit `rcases h with ⟨h₁, h₂⟩` zerlegen."

HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : B ∧ C) : (A ∨ C) =>
"**Robo** Das `∧` in der Annahme kannst Du mit `rcases h with ⟨h₁, h₂⟩` zerlegen."

-- TODO: Hint nur Anhand der Annahmen?

HiddenHint (A : Prop) (B : Prop) : A ∨ B =>
"**Robo** `left` oder `right`?"

Conclusion
"
**Robo** Bravo!  Jetzt aber nichts wie weg hier, bevor sich eine neue Schlange bildet!

Logisinde ist in der Zwischenzeit eingeschlafen, und ihr stehlt euch heimlich davon.
"

NewTactics left right assumption constructor rcases rfl contradiction trivial
DisabledTactics tauto
