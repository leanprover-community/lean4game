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
Ihr habt nun alle Fragen aus dem königlichen Päckchen beantwortet, und die Formalosophinnen applaudieren.  Dann wollen Sie aber auch noch ein paar Fragen stellen, aber sie können sich nicht einigen, welche.  
Ihr heute abwechselnd die Rufe „Even“ und „Odd“ aus der Menge heraus. Deshalb zeigt Dir Robo vorsichtshalber schon einmal die entsprechenden Definitionen an:

```
def Even (n : ℕ) : Prop := ∃ r, n = r + r
```

und

```
def Odd (n : ℕ) : Prop := ∃ r, n = 2 * r + 1
```

Schließlich taucht von irgendwo aus der Menge folgendes Papier auf:
"

Statement even_square (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  Hint "**Robo**: Du kannst Dir mit `unfold Even` auch hier auf dem Papier die Definition sehen."
  Branch
    unfold Even
    Hint "Robo**: Am besten machst Du auch noch `unfold Even at h`, damit Du verstehst, was los ist."
  Hint "**Robo**: Wie Du oben siehst, ist `Even n` dadurch definiert,
    dass ein `r` existiert so dass `r + r = n` ist. Am besten
    öffnest du diese Definition mit `unfold Even at *` einmal.
    Dann siehst Du besser, was los ist. "
  unfold Even at *
  Hint "**Du**: Also von `{h}` weiß ich jetzt, dass ein `r` existiert, so dass `r + r = n` …

  **Robo**: Mit `rcases h with ⟨r, hr⟩` kannst du dieses `r` tatsächlich einführen."
  rcases h with ⟨r, hr⟩
  Hint "**Du**: Und jetzt muss ich eine passende Zahl finden, so dass `x + x = n^2`?

  **Robo**: Genau. Und mit `use _` gibst du diese Zahl an."
  Hint (hidden := true) "**Robo**: Also sowas ähnliches wie `use 4 * r ^ 3`, aber ich kann
  Dir leider nicht sagen, welche Zahl passt.
  "
  Branch
    rw [hr]
    Hint "**Robo**: Das geht auch, jetzt musst Du aber wirklich `use` verwenden."
    use 2 * r ^ 2
    ring
  use 2 * r ^ 2
  Hint "**Du**: Ah, und jetzt `ring`!

  **Robo**: Aber zuerst musst Du noch mit
  `rw` `n` durch `r + r` ersetzen, da `ring` das sonst nicht weiß."
  rw [hr]
  ring

-- TODO: [Comment] For me the expected behaviour of `(strict := true)` would
-- be that it distinguishes between the defEq states while `(strict := false)`
-- would show the hint regardless of a `unfold Even`.

NewTactic unfold use
NewDefinition Even Odd

Conclusion "Applaus!"
