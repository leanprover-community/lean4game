import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
World "SetFunction"
Level 1

Title ""

open Set

set_option tactic.hygienic false

Introduction
"
Das Bild einer Funktion ist eine Menge, die als `f '' S` geschrieben wird.
In der Mathe ist das normalerweise als $f(S)$ geschrieben.

Mit `ext i` kann man Gleichheit von Mengen angehen.
"


-- Wenn man mit Abildungen auf Mengen arbeitet, muss man in Lean etwas aufpassen, um
-- die Typen (z.B. `(U : Type _)`) und Mengen von diesen Typen (z.B. `(S : Set U)`)
-- zu unterscheiden.

-- Abbildungen sind prinzipiell immer auf Typen definiert. Wenn eine Funktion nicht
-- auf dem ganzen Typen definiert ist, hat man prinzipiell zwei Optionen:

-- 1. Nach dem Motto \"Junk in, junk out\" werden in der Mathlib Funktionen
-- oft einfach auf irgendwas gesetzt wenn sie nicht definiert sind, so gibt `1 / 0` in `ℕ`
-- einfach `0`. Dies funktioniert, weil dann alle relevanten Theoreme, die von `x / n`
-- handeln, dann Annahmen der Form `(h : n ≠ 0)` haben.
-- 2. Man kann auch Funktionen auf *Subtypen* definieren, also z.B. auf `ℕ+`.


--     /- Image of Union -/
-- lemma image_unionₓ

Statement
""
    (S T : Set ℕ) (f : ℕ → ℕ) : (f '' S) ∪ (f '' T) = f '' (S ∪ T) := by
  Hint "Fang mal mit `ext i` an."
  ext i
  rw [mem_union]
  simp_rw [mem_image]
  constructor
  intro h
  rcases h with ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩
  use x
  constructor
  apply mem_union_left
  assumption
  assumption
  use x
  constructor
  apply mem_union_right
  assumption
  assumption
  rintro ⟨x, hx, hx'⟩
  rw [mem_union] at hx
  rcases hx with hx | hx
  left
  use x
  constructor
  assumption
  assumption
  right
  use x
  constructor
  assumption
  assumption

NewTactic ext
LemmaTab "Set"
