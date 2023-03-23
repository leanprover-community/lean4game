import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import Mathlib.Algebra.Parity

set_option tactic.hygienic false

Game "TestGame"
World "Predicate"
Level 7

Title "Gerade/Ungerade"

Introduction
"
**Du**: Aber, das sagt doch gar nichts aus, genau das gleiche könnte ich für `Odd`
auch sagen. Hier seht!
"

Statement odd_square (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  unfold Odd at *
  rcases h with ⟨r, hr⟩
  Hint "**Robo**: Ich hab noch einen Trick auf Lager:
  Wenn du jetzt herausfinden willst, welche Zahl du einsetzen musst, könntest
  du schon jetzt mit `rw [{hr}]` weitermachen…"
  rw [hr]
  Hint "**Robo**: Wenn du jetzt `ring` benötigst, dann schreibt es einfach alles in
  Normalform um, das hilft beim vergleichen."
  ring
  Hint "**Du**: Was bedeutet `ring_nf`?

  **Robo**: Wenn man `ring` nicht am Schluss benützt, sollte man stattdessen `ring_nf`
  schreiben, aber die funktionieren praktisch gleich."
  use 2 * (r + r ^ 2)
  ring

-- TODO: Allow `ring_nf` as part of `ring`.

Conclusion "**Evenine**: Tatsächlich. Vielleicht sind wir gar nich tso unterschiedlich. Könntet
ihr mal mit ihm reden gehen?"
