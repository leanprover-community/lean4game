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
  Hint (hidden := true) "**Robo**: mit `rcases h with ⟨r, hr⟩` kannst du wieder
  das `r` nehmen, das laut Annahme existieren muss.

  **Robo**: Oder aber, du fängst mit `unfold Odd at *` an."
  Branch
    unfold Odd
    Hint "**Robo**: Mit `unfold Odd at *` öffnest du alle Definitionen von `Odd`."
    unfold Odd at *
  Branch
    unfold Odd at *
    Hint (hidden := true) "**Robo**: mit `rcases h with ⟨r, hr⟩` kannst du wieder
    das `r` nehmen, das laut Annahme existieren muss."
    rcases h with ⟨r, hr⟩
    Hint "**Robo**: Ich hab noch einen Trick auf Lager:
    Wenn du jetzt noch nicht weißt, welche Zahl du einsetzen musst, könntest
    du schon jetzt mit `rw [{hr}]` weitermachen …"
    Branch
      rw [hr]
      Hint "**Robo**: Wenn du jetzt `ring` brauchst, dann schreibt es einfach alles in
      Normalform um, das hilft beim Vergleichen."
      ring
      Hint "**Du**: Was bedeutet `ring_nf`?

      **Robo**: Wenn man `ring` nicht am Schluss benützt, sollte man stattdessen `ring_nf`
      schreiben, aber die funktionieren praktisch gleich."
    use 2 * (r + r ^ 2)
    ring
  rcases h with ⟨r, hr⟩
  Hint "**Robo**: Ich hab noch einen Trick auf Lager:
    Wenn du jetzt noch nicht weißt, welche Zahl du einsetzen musst, könntest
    Du schon jetzt mit `rw [{hr}]` weitermachen…"
  Branch
    rw [hr]
    Hint "**Robo**: Wenn du jetzt `ring` brauchst, dann schreibt es einfach alles in
    Normalform um, das hilft beim Vergleichen."
    ring
    Hint "**Du**: Was bedeutet `ring_nf`?

    **Robo**: Wenn man `ring` nicht am Schluss benützt, sollte man stattdessen `ring_nf`
    schreiben, aber die funktionieren praktisch gleich."
  use 2 * (r + r ^ 2)
  rw [hr]
  ring
-- TODO: Allow `ring_nf` as part of `ring`.

Conclusion "Applaus!"

-- TODO: THis level would be a good example where a `Hint (defeq := true)` would be desirable
-- in order to reduce the number of hints that are duplicated.
