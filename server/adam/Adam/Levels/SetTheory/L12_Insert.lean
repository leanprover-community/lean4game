import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
World "SetTheory"
Level 12

Title "Konkrete Mengen"

Introduction
"
Nun schauen wir uns konkrete Mengen an. Man schreibt diese mit
geschweiften Klammern: `{0, 4, 117, 3}`. Meistens muss man
den Typ explizit angeben, weil Lean nicht weiss, ob man mit `Set` (Mengen)
oder `Finset` (endliche Mengen) arbeiten möchte: `({4, 9} : Set ℕ)`.

`Finset` schauen wir uns später an.

Um mit expliziten Mengen zu arbeiten, ist die Implementationsweise wichtig.

Intern ist eine Menge `{0, 9, 5, 2}` iterativ als Vereinigung von
Singletons definiert: `{0} ∪ ( {9} ∪ ( {5} ∪ {2} ))`.

Die folgende Aufgabe ist entsprechend mit `rfl` lösbar.
"

open Set

Statement
"Die Menge $\\{4, 9\\}$ ist per Definition $\\{4}\\cup\\{9\\}$." :
    ({4, 9} : Set ℕ) = Set.insert 4 {9} := by
  rfl

OnlyTactic rfl
LemmaTab "Set"
