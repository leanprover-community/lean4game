import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import Mathlib.Algebra.Parity

set_option tactic.hygienic false

Game "Adam"
World "Predicate"
Level 7

Title "Gerade/Ungerade"

Introduction
"
Sofort taucht das nächste Blatt auf.  Anscheinend hatten sie sich auf einen Kompromiss geeinigt.
"

Statement odd_square (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  unfold Odd at *
  rcases h with ⟨r, hr⟩
  Hint "**Robo**: Ich hab noch einen Trick auf Lager:
  Wenn du jetzt herausfinden willst, welche Zahl Du einsetzen musst, könntest
  Du schon jetzt mit `rw [{hr}]` weitermachen …"
  rw [hr]
  Hint "**Robo**: Wenn Du jetzt `ring` benötigst, dann schreibt es einfach alles in
  Normalform um, das hilft beim Vergleichen."
  ring
  Hint "**Du**: Was bedeutet `ring_nf`?

  **Robo**: Wenn man `ring` nicht am Schluss benützt, sollte man stattdessen `ring_nf`
  schreiben, aber die funktionieren praktisch gleich."
  use 2 * (r + r ^ 2)
  ring

-- TODO: Allow `ring_nf` as part of `ring`.

Conclusion "Applaus!"

