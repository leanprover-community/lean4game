import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Nat"
Level 3

Title "Gerade/Ungerade"

Introduction
"
Gerade/ungerade werden in Lean wie folgt definiert:
```
def even (n : ℕ) : Prop := ∃ r, n = 2 * r
def odd (n : ℕ) : Prop := ∃ r, n = 2 * r + 1
```
Also dadurch, dass ein `(r : ℕ)` existiert sodass `n = 2 * r (+1)`.
Beachte das Komma `,` welches die Variablen des `∃` (`\\exists`) von der Aussage trennen.

Hierzu gibt es 3 wichtige Taktiken:

1) Definitionen wie `even` kann man mit `unfold even at *` im Infoview einsetzen.
   Das ändert Lean-intern nichts und ist nur für den Benutzer. Man kann auch einen
   Term `(h : even x)` einfach so behandeln als wäre es ein Term `(h : ∃ r, x = 2 * r)`.
2) Bei einer Annahme `(h : ∃ r, ...)` kann man mit `rcases h with ⟨y, hy⟩` ein solches `y`
   Auswählen, dass die Annahme `h` erfüllt.
3) Bei einem `∃` im Goal muss man ein Element `y` angeben, welches diese Aussage erfüllen
   soll. Das macht man mit `use y`
"

Statement even_square
      "Wenn $n$ gerade ist, dann ist $n^2$ gerade."
      (n : ℕ) (h : even n) : even (n ^ 2) := by
  unfold even at *
  rcases h with ⟨x, hx⟩
  use 2 * x ^ 2
  rw [hx]
  ring

Message (n : ℕ) (h : even n) : even (n ^ 2) =>
"Wenn du die Definition von `even` nicht kennst, kannst du diese mit `unfold even` oder
`unfold even at *` ersetzen.
Note: Der Befehl macht erst mal nichts in Lean sondern nur in der Anzeige. Der Beweis funktioniert
genau gleich, wenn du das `unfold` rauslöscht."

Message (n : ℕ) (h : ∃ r, n = 2 * r) : ∃ r, n ^ 2 = 2 * r =>
"Ein `∃ x, ..` in den Annahmen kann man wieder mit `rcases h with ⟨x, hx⟩` aufteilen, und
ein `x` erhalten, dass die Aussage erfüllt."

Message (n : ℕ) (x : ℕ) (hx : n = x + x) : ∃ r, n ^ 2 = 2 * r =>
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
Lemmas even odd
