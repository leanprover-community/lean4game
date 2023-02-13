import TestGame.Metadata
import Std.Tactic.RCases

set_option tactic.hygienic false

Game "TestGame"
World "Proposition"
Level 11

Title "Und"

Introduction
"
Hat man ein UND `(h : A ∧ B)` in den Annahmen, möchte man normalerweise die einzelnen Felder
(linke/rechte Seite) einzeln verwenden. Dazu hat man zwei Möglichkeiten:

1. Mit `h.left` und `h.right` (oder `h.1` und `h.2`) kann man die Felder direkt auswählen.
2. Mit `rcases h with ⟨h₁, h₂⟩` kann man die Struktur `h` zerlegen und man erhält zwei
   separate Annahmen `(h₁ : A)` und `(h₂ : B)`

Die Klammern `⟨·,·⟩` sind `\\<` und `\\>` oder `\\<>` als Paar.
"

Statement "Benutze `rcases` um das UND in `(h : A ∧ (B ∧ C))` zu zerlegen und beweise, dass $B$ wahr ist."
    (A B C : Prop) (h : A ∧ (B ∧ C)) : B := by
  rcases h with ⟨_, ⟨g , _⟩⟩
  assumption

HiddenHint (A : Prop) (B : Prop) (C : Prop) (h : A ∧ (B ∧ C)) : B =>
"Du kannst mit `rcases` auch verschachtelt mehrere Strukturen in einem Schritt zerlegen:
`rcases h with ⟨h₁, ⟨h₂ , h₃⟩⟩`."

HiddenHint (A : Prop) (hA : A) : A =>
  "Du hast einen Beweis dafür in den *Annahmen*."

NewTactics rcases
DisabledTactics tauto

-- Statement
--     "Zeige $(A \\land (A \\Rightarrow B)) \\iff (A \\land B)$."
--     (A B : Prop) : (A ∧ (A → B)) ↔ (A ∧ B) := by
--   constructor
--   intro h
--   rcases h with ⟨h₁, h₂⟩
--   constructor
--   assumption
--   apply h₂
--   assumption
--   intro h
--   rcases h with ⟨h₁, h₂⟩
--   constructor
--   assumption
--   intro
--   assumption

-- Hint (A : Prop) (B : Prop) : A ∧ (A → B) ↔ A ∧ B =>
-- "`↔` oder `∧` im Goal kann man mit `constructor` zerlegen."

-- Hint (A : Prop) (B : Prop) : A ∧ (A → B) → A ∧ B =>
-- "Hier würdest du mit `intro` die Implikation angehen.

-- (Experten können mit `intro ⟨h₁, h₂⟩` im gleichen Schritt noch ein `rcases` auf
-- das UND in der Implikationsannahme)"

-- -- if they don't use `intro ⟨_, _⟩`.
-- Hint (A : Prop) (B : Prop) (h : A ∧ (A → B)) : A ∧ B =>
-- "Jetzt erst mal noch schnell die Annahme `A ∧ (A → B)` mit `rcases` aufteilen."

-- HiddenHint (A : Prop) (B : Prop) (hA : A) (h : A → B) : B =>
-- "Wie wär's mit `apply`? Hast du ne Implikation, die anwendbar ist?"

-- -- Rückrichtung
-- Hint (A : Prop) (B : Prop) : A ∧ B → A ∧ (A → B) =>
-- "Das Goal ist ne Implikation $\\ldots \\Rightarrow \\ldots$
-- Da hilft `intro`.

-- (auch hier kann man wieder mit `intro ⟨ha, hb⟩` gleich noch die Premisse zerlegen.)"




-- -- if they don't use `intro ⟨_, _⟩`.
-- Hint (A : Prop) (B : Prop) (h : A ∧ B) : A ∧ (A → B) =>
-- "Jetzt erst mal noch schnell die Annahme `A ∧ B` mit `rcases` zerlegen."

-- Hint (A : Prop) (B : Prop) (hA : A) (h : A → B) : A ∧ B =>
-- "Wieder in Einzelteile zerlegen..."

-- Hint (A : Prop) (B : Prop) (ha : A) (hb : B) : A ∧ (A → B) =>
-- "Immer das gleiche ... noch mehr zerlegen."

-- -- Hint (A : Prop) (B : Prop) (h₁: A) (h₂: B) : A → B =>
-- -- "Das ist jetzt vielleicht etwas verwirrend: Wir wollen die Implikation `A → B` zeigen,
-- -- wissen aber, dass `B` immer wahr ist (habe eine Annahme der Form `(hB : B)`).

-- -- Mit intro können wir einfach nochmal annehmen, dass `A` wahr ist. Es stört uns nicht,
-- -- dass wir das schon wissen und auch gar nicht brauchen. Damit müssen wir nur noch zeigen,
-- -- dass `B` wahr ist."



-- -- TODO


-- Tactics apply rcases
-- Tactics assumption
