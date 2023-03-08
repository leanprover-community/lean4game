import TestGame.Metadata

import TestGame.Options.BigOperators
import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "Sum"
Level 2

Title "endliche Summe"

Introduction
"
Generell sind aber nur solche Lemmas `@[simp]` markiert, klar eine Vereinfachung darstellen.

So ist ein Lemma wie `Finset.sum_add_distrib` kein `simp`-Lemma, da beide Seiten je
nach Situation bevorzugt sein könnte:

$$
  \\sum_{i = 0}^n a_i + b_i = \\sum_{i = 0}^n a_i + \\sum_{j = 0}^n b_j
$$

Dieses Lemma kann aber mit `rw` angewendet werden.
"

open BigOperators

Statement
"Zeige dass $\\sum_{i=0}^{n-1} (i + 1) = n + \\sum_{i=0}^{n-1} i$."
    (n : ℕ) : ∑ i : Fin n, ((i : ℕ) + 1) = n + (∑ i : Fin n, (i : ℕ)) := by
  rw [Finset.sum_add_distrib]
  Hint "Die zweite Summe `∑ x : Fin n, 1` kann `simp` zu `n` vereinfacht werden."
  simp
  Hint "Bis auf Umordnung sind jetzt beide Seiten gleich, darum kann `ring` das Goal schließen.

    Alternativ kann man auch mit `rw [add_comm]` dies explizit umordnen."
  ring

NewLemmas Finset.sum_add_distrib add_comm
