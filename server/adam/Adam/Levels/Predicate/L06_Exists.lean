import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import Mathlib.Algebra.Parity

set_option tactic.hygienic false

Game "Adam"
World "Predicate"
Level 6

Title "Gerade/Ungerade"

Introduction
"
Am nächsten Tag erklärt euch *Evenine*, dass es auf dem Mond zwei Gruppierungen gibt,
ihre und die ihres Halbbruders *Oddeus*. Die Mottos sind

```
def Even (n : ℕ) : Prop := ∃ r, n = r + r
```

und

```
def Odd (n : ℕ) : Prop := ∃ r, n = 2 * r + 1
```

**Evenine**: Hier, ich zeige euch mal etwas was man bei uns machen kann:
"

Statement even_square (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  Branch
    unfold Even
    Hint "Rob**: Am besten machst du auch noch `unfold Even at h`, damit du verstehst was los ist."
  Hint "**Robo**: Wie du oben siehst, ist `Even n` dadurch definiert,
    dass ein `r` existiert so dass `r + r = n`. Am besten
    öffnest du diese Definition mit `unfold Even at *` einmal, dann siehst du besser, was los ist. "
  unfold Even at *
  Hint "**Du**: Also von `{h}` weiss ich jetzt dass ein `r` existiert, so dass `r + r = n`…

  **Robo**: Mit `rcases h with ⟨r, hr⟩` kannst du dieses `r` tatsächlich einführen."
  rcases h with ⟨r, hr⟩
  Hint "**Du**: Und jetzt muss ich eine passende Zahl finden, so dass `x + x = n^2`?

  **Robo**: Genau. Und mit `use _` gibst du diese Zahl an."
  Hint (hidden := true) "**Robo**: Also sowas ähnliches wie `use 4 * r ^ 3`, aber ich kann
  dir leider nicht sagen, welche Zahl passt.
  "
  Branch
    rw [hr]
    Hint "**Robo**: Das geht auch, jetzt musst du aber wirklich `use` verwenden."
    use 2 * r ^ 2
    ring
  use 2 * r ^ 2
  Hint "**Du**: Ah und jetzt `ring`!

  **Robo**: Aber zuerst must du noch mit
  `rw` `n` durch `r + r` ersetzen, da `ring` das sonst nicht weiss."
  rw [hr]
  ring

-- TODO: [Comment] For me the expected behaviour of `(strict := true)` would
-- be that it distinguishes between the defEq states while `(strict := false)`
-- would show the hint regardless of a `unfold Even`.

NewTactic unfold use
NewDefinition Even Odd

Conclusion "**Evenine**: Seht ihr?"
