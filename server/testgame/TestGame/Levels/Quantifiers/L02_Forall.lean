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

Statement : ∀ (x : ℕ), 1 = x ^ 2 → 1 = x := by
  intro x h



-- TODO: Server PANIC because of the `even`.
--
-- Message (n : ℕ) (h : even n) : even (n ^ 2) =>
-- "Wenn du die Definition von `even` nicht kennst, kannst du diese mit `unfold even` oder
-- `unfold even at *` ersetzen.
-- Note: Der Befehl macht erst mal nichts in Lean sondern nur in der Anzeige. Der Beweis funktioniert
-- genau gleich, wenn du das `unfold` rauslöscht."

Message (n : ℕ) (h : ∃ r, n = r + r) : ∃ r, n ^ 2 = r + r =>
"Ein `∃ x, ..` in den Annahmen kann man wieder mit `rcases h with ⟨x, hx⟩` aufteilen, und
ein `x` erhalten, dass die Aussage erfüllt."

Message (n : ℕ) (x : ℕ) (hx : n = x + x) : ∃ r, n ^ 2 = r + r =>
"Bei einem `∃ x, ..` im Goal hingegen, muss man mit `use y` das Element angeben, dass
die Aussage erfüllen soll."

Message (n : ℕ) (x : ℕ) (hx : n = x + x) : ∃ r, (x + x) ^ 2 = r + r =>
"Bei einem `∃ x, ..` im Goal hingegen, muss man mit `use y` das Element angeben, dass
die Aussage erfüllen soll."

Message (n : ℕ) (x : ℕ) (hx : n = x + x) : n ^ 2 = 2 * x ^ 2 + 2 * x ^ 2 =>
"Prinzipiell löst `ring` simple Gleichungen wie diese. Allerdings musst du zuerst `n` zu
`x + x` umschreiben..."

Message (n : ℕ) (x : ℕ) (hx : n = x + x) : (x + x) ^ 2 = 2 * x ^ 2 + 2 * x ^ 2 =>
"Die Taktik `ring` löst solche Gleichungen."

Tactics unfold rcases use rw ring
