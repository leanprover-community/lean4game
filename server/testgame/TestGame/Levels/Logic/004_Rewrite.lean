import TestGame.Metadata

Game "Introduction"
World "Tactic"
Level 4

Title "Rewrite"

Introduction
"
Oft sind aber die Annahmen nicht genau das, was man zeigen will, sondern helfen einem
nur, dorthin zu kommen.

Wenn man eine Annahme `(h : X = Y)` hat, die sagt, dass `X` und `Y` gleich sind,
kann man die Taktik `rw` (steht für 'rewrite') brauchen um im Goal
das eine durch das andere zu ersetzen.
"

Statement (a b c d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  rewrite [h₁]
  rw [←h₂]
  assumption

-- Gleich am Anfang anzeigen.
Message (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c =>
"Wenn man eine Annahme `(h₁ : c = d)` hat, kann man mit `rw [h₁]` (oder `rewrite [h₁]`) das erste
`c` im Goal mit `d` ersetzen."

Hint (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c =>
"Die kleinen Zahlen `h₁ h₂ h₃` werden in Lean oft verwendet und man schreibt diese mit
`\\1`, `\\2`, `\\3`, …"

Message (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = d =>
"Mit `rw [← h₂]` (`\\l`, also klein L wie \"left\") kann man eine Hypotheses
`(h₂ : a = b)` rückwärts anwenden und `b` durch `a` ersetzen."

-- TODO: Muss ich das wirklich mehrmals auflisten?
Message (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : a = a =>
"Der Hauptunterschied zwischen `rw` und `rewrite` ist, dass das erste automatisch versucht,
anschliessend `rfl` anzuwenden. Bei `rewrite` musst du `rfl` explizit noch aufrufen."
Message (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = b =>
"Der Hauptunterschied zwischen `rw` und `rewrite` ist, dass das erste automatisch versucht,
anschliessend `rfl` anzuwenden. Bei `rewrite` musst du `rfl` explizit noch aufrufen."
Message (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : c = c =>
"Der Hauptunterschied zwischen `rw` und `rewrite` ist, dass das erste automatisch versucht,
anschliessend `rfl` anzuwenden. Bei `rewrite` musst du `rfl` explizit noch aufrufen."
Message (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : d = d =>
"Der Hauptunterschied zwischen `rw` und `rewrite` ist, dass das erste automatisch versucht,
anschliessend `rfl` anzuwenden. Bei `rewrite` musst du `rfl` explizit noch aufrufen."

Conclusion "Übrigens, mit `rw [h₁] at h₂` kann man auch eine andere Annahme umschreiben
anstatt dem Goal."
-- TODO: Das macht es doch unmöglich mit den Messages...

Tactics assumption
--Tactics rw
