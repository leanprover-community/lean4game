import TestGame.Metadata
import Std.Tactic.RCases

set_option tactic.hygienic false

Game "TestGame"
World "Logic"
Level 13

Title "Und"

Introduction
"
Das logische UND `A ∧ B` (`\\and`) funktioniert sehr ähnlich zum Iff (`↔`).
Grund dafür ist, dass `A ∧ B` auch eine Struktur aus zwei Teilen ist, nämlich
der linken und rechten Seite.

Man can also genau gleich `constructor` und `rcases` anwenden, ebenso kann man
`.1` und `.2` für die Einzelteile brauchen, diese heissen lediglich
`h.left` und `h.right` anstatt `.mp` und `.mpr`.
"

Statement
    "Zeige $(A \\land (A \\Rightarrow B)) \\iff (A \\land B)$."
    (A B : Prop) : (A ∧ (A → B)) ↔ (A ∧ B) := by
  constructor
  intro h
  rcases h with ⟨h₁, h₂⟩
  constructor
  assumption
  apply h₂
  assumption
  intro h
  rcases h with ⟨h₁, h₂⟩
  constructor
  assumption
  intro
  assumption

Message (A : Prop) (B : Prop) : A ∧ (A → B) ↔ A ∧ B =>
"`↔` oder `∧` im Goal kann man mit `constructor` zerlegen."

Message (A : Prop) (B : Prop) : A ∧ (A → B) → A ∧ B =>
"Hier würdest du mit `intro` die Implikation angehen.

(Experten können mit `intro ⟨h₁, h₂⟩` im gleichen Schritt noch ein `rcases` auf
das UND in der Implikationsannahme)"

-- if they don't use `intro ⟨_, _⟩`.
Message (A : Prop) (B : Prop) (h : A ∧ (A → B)) : A ∧ B =>
"Jetzt erst mal noch schnell die Annahme `A ∧ (A → B)` mit `rcases` aufteilen."

Hint (A : Prop) (B : Prop) (hA : A) (h : A → B) : B =>
"Wie wär's mit `apply`? Hast du ne Implikation, die anwendbar ist?"

-- Rückrichtung
Message (A : Prop) (B : Prop) : A ∧ B → A ∧ (A → B) =>
"Das Goal ist ne Implikation $\\ldots \\Rightarrow \\ldots$
Da hilft `intro`.

(auch hier kann man wieder mit `intro ⟨ha, hb⟩` gleich noch die Premisse zerlegen.)"




-- if they don't use `intro ⟨_, _⟩`.
Message (A : Prop) (B : Prop) (h : A ∧ B) : A ∧ (A → B) =>
"Jetzt erst mal noch schnell die Annahme `A ∧ B` mit `rcases` zerlegen."

Message (A : Prop) (B : Prop) (hA : A) (h : A → B) : A ∧ B =>
"Wieder in Einzelteile zerlegen..."

Message (A : Prop) (B : Prop) (ha : A) (hb : B) : A ∧ (A → B) =>
"Immer das gleiche ... noch mehr zerlegen."

-- Message (A : Prop) (B : Prop) (h₁: A) (h₂: B) : A → B =>
-- "Das ist jetzt vielleicht etwas verwirrend: Wir wollen die Implikation `A → B` zeigen,
-- wissen aber, dass `B` immer wahr ist (habe eine Annahme der Form `(hB : B)`).

-- Mit intro können wir einfach nochmal annehmen, dass `A` wahr ist. Es stört uns nicht,
-- dass wir das schon wissen und auch gar nicht brauchen. Damit müssen wir nur noch zeigen,
-- dass `B` wahr ist."



-- TODO


Tactics apply rcases
Tactics assumption
