import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring


Game "TestGame"
World "Quantors"
Level 9

Title "Kontraposition"

Introduction
"
Bei einem `∀ x,` im Goal kann man mit `intro x` annehmen, dass man ein solches `x` hat.

Ein `(h : ∀ x, _)` in den Annahmen kann ....
"

-- TODO: `even`/`odd` sind in Algebra.Parity. Not ported yet
def even (a : ℕ) : Prop := ∃ r, a = r + r
def odd (a : ℕ) : Prop := ∃ k, a = 2*k + 1

Statement : ∀ (x : ℕ), even x → even (x + 2) := by
  intro x h
  unfold even at *
  rcases h with ⟨y, hy⟩
  use y + 1
  rw [hy]
  ring

-- Message (n : ℕ) (h : even n) : even (n ^ 2) =>
-- "Wenn du die Definition von `even` nicht kennst, kannst du diese mit `unfold even` oder
-- `unfold even at *` ersetzen.
-- Note: Der Befehl macht erst mal nichts in Lean sondern nur in der Anzeige. Der Beweis funktioniert
-- genau gleich, wenn du das `unfold` rauslöscht."

Tactics unfold rcases use rw ring intro
