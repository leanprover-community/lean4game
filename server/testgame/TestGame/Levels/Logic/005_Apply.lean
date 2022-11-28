import TestGame.Metadata

Game "Introduction"
World "Tactic"
Level 5

Title "Implikation"

Introduction
"
Wie wir schon gesehen haben, wir eine logische Aussage als `(A : Prop)` geschrieben, und
die Annahme, dass `A` wahr ist als `(hA : A)`, also `hA` ist sozusagens ein Beweis der
Aussage `A`.

Logische Aussagen können einander implizieren. Wir kennen hauptsächlich zwei Zeichen dafür:
`A ↔ B` (`\\iff`) bedeutet \"Genau dann wenn\" und `A → B` (`\\to`) bedeutet \"`A` impliziert `B`\".

Wenn man Aussage `B` beweisen will und eine Implikationsannahme `(h : A → B)` hat, dann kann man
diese mit `apply h` anwenden.
Auf Papier würde man schreiben, \"es genügt zu zeigen, dass `A` stimmt, denn `A` impliziert `B`\".
"

Statement (A B : Prop) (hA : A) (g : A → B) : B := by
  apply g
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
