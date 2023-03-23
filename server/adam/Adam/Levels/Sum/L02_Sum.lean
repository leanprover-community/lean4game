import TestGame.Metadata

import TestGame.ToBePorted
import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "Sum"
Level 2

Title "endliche Summe"

Introduction
"
Während euch die Person zu einem besonders herausragenden Steinturm führt, löchert
sie euch noch weiter mit Fragen.
"

open BigOperators

Statement
    "$\\sum_{i=0}^{n-1} (i + 1) = n + \\sum_{i=0}^{n-1} i$."
    (n : ℕ) : ∑ i : Fin n, ((i : ℕ) + 1) = n + (∑ i : Fin n, (i : ℕ)) := by
  -- Hint "**Du**: Hmm, wieder `simp`?

  -- **Robo**: Nicht ganz. `simp` benützt nur Lemmas, die klar eine Vereinfachung darstellen,
  -- und in deiner Bibliothek mit `@[simp]` markiert wird. Hier brauchen wir eine andere
  -- Umformung:

  -- $$
  -- \\sum_\{i = 0}^n a_i + b_i = \\sum_\{i = 0}^n a_i + \\sum_\{j = 0}^n b_j
  -- $$

  -- **Robo*: Da unklar ist, welche Seite \"einfacher\" ist, wird so ein Lemma nicht mit
  -- `@[simp]` markiert. Das heisst du musst `Finset.sum_add_distrib` mit `rw`
  -- explizit anwenden.
  -- "
  rw [Finset.sum_add_distrib]
  Hint "**Robo**: Die zweite Summe `∑ x : Fin n, 1` kann jetzt aber mit
  `simp` zu `n` vereinfacht werden."
  simp
  Hint "**Robo**: Bis auf Umordnung sind jetzt beide Seiten gleich!

  **Du**: Dann greift jetzt wohl `ring`!

  **Robo**: Genau! Und alternativ könntest du mit `rw [add_comm]` die Arbeit von `ring`
  auch manuell machen."
  ring

NewLemma Finset.sum_add_distrib add_comm

Conclusion "Eure Begleitung scheint mit der Antwort zu frieden zu sein und zeigt
freudig an dem Turm empor, den ihr soeben erreicht habt."
