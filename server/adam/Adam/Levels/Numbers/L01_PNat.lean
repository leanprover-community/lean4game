import Adam.Metadata
import Mathlib

Game "Adam"
World "Numbers"
Level 1

Title ""

Introduction
"
-- Level name : Positive natürliche Zahlen

import data.pnat.basic

/-
In diesem Level lernst du neben `ℕ` weitere Arten von
Zahlen kennen: `ℕ+`,`ℤ`, `ℚ`, `ℝ`, `ℂ`.

Manchmal sieht man in der Literatur Diskussionen, ob die natürlichen Zahlen jetzt bei `0` oder `1`
anfangen, wobei zumindest in der formalisierten Mathematik (z.B. ZFC-Mengenlehre)
eigentlich immer `ℕ = {0, 1, 2, 3, …}` definiert wird.

So ist auch in Lean `1` als `0.succ` und `2 = 1.succ = 0.succ.succ` definiert und
Lean hat eine separate Notation `ℕ+` (oder `pnat`) für alle *positiven* natürlichen Zahlen.

Dies ist als Sub-Typ von `ℕ` definiert:
`def pnat := {n : ℕ // 0 < n}`

ein Element `(p : ℕ+)` besteht also aus einer natürlichen Zahl `(p.val : ℕ)`
(oder auch `p.1`, wobei `p.val` bevorzugt ist) sowie einem Beweis, dass diese positiv ist,
`p.property` (oder `p.2`).

Solche Strukturen mit mehr als einem Feld kann man in Lean mit dem anonymen Konstruktor `⟨_, _⟩`
erstellen, wie du schon einmal beim `∃` gesehen hast: `(⟨n, h⟩ : ℕ+)`
"

Statement
""
    (a : ℕ+) : (a : ℕ) ≠ 0 := by
  apply ne_of_gt
  rcases a with ⟨a, ha⟩
  assumption


-- -/

-- /- Hint : a.property
-- `have ha := a.property` speichert die `ℕ+`-Eigenschaft dass `0 < a.val`
-- gilt als neue Variable.
-- -/

-- /- Hint : ne_of_lt/ne_of_gt
-- `a < b → a ≠ b`
-- oder
-- `a < b → b ≠ a`

-- alternativ kannst du auch mit `symmetry` ein symmetrischen Goal drehen.
-- -/

-- /- Lemma : no-side-bar
-- Beweise.
-- -/
-- example (a : ℕ+) : (a : ℕ) ≠ 0 :=
-- begin
--   have ha := a.property,
--   symmetry,
--   apply ne_of_lt,
--   exact ha,
-- end

-- /- Axiom : ne_of_lt
-- `a < b → a ≠ b`.
-- -/

-- /- Axiom : ne_of_gt
-- `a < b → b ≠ a`.
-- -/

-- /- Tactic : symmetry
-- Dreht ein symmetrisches Goal wie `A = B`, `A ≠ B`, `A ↔ B`, ...
-- -/
