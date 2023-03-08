import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 3

Title "Komposition"

Introduction
"
Endlich kommt ihr zur Bibliothek. Komischerweise stehen an der Tür
zwei Wächtern. Der eine zeigt euch ein Blatt mit

```
def f : ℚ → ℚ := fun x ↦ 5 * x
```

der andere eines mit

```
def g : ℚ → ℚ := fun x ↦ if 0 ≤ x then 2*x else 0
```

und gibt Dir ein Blatt mit einer einzelnen Zeile am oberen Ende.
"

open Set

namespace LevelFunction4

def f : ℚ → ℚ := fun x ↦ 5 * x
def g : ℚ → ℚ := fun x ↦ if 0 ≤ x then 2*x else 0

Statement ""
    : f ∘ g = g ∘ f := by
  funext x
  simp_rw [Function.comp_apply]
  unfold g
  by_cases 0 ≤ x
  have h' : 0 ≤ f x
  unfold f
  linarith
  rw [if_pos h', if_pos h]
  unfold f
  ring
  have h' : ¬ (0 ≤ f x)
  unfold f
  linarith
  rw [if_neg h, if_neg h']
  unfold f
  ring

NewTactic funext by_cases simp_rw linarith

NewLemma not_le if_pos if_neg


Hint : f ∘ g = g ∘ f =>
"
**Robo**: Schau mal, die beiden haben zwei Funktionen, eine davon mit stückweiser Definition.

**Du**: Und ich soll zeigen, dass die beiden vertauschbar sind?

**Robo**: Genau, am besten wählst du mit `funext x` ein beliebiges Element aus, und zeigst das
dann für dieses.
"

-- TODO : This does not trigger.
-- TODO: These 5 hints should be mutually exclusive. i.e. they should not trigger
-- if a assumption is missing.
Hint (x : ℚ) : (f ∘ g) x = (g ∘ f) x =>
"
**Du**: Ah und jetzt kann ich erst einmal `(g ∘ f) {x}` zu `g (f {x})` umschreiben?

**Robo**: Mit `simp_rw` geht das übrigens schneller.

**Robo**: Und danach willst du eien Fallunterscheidung
machen, `by_cases h : 0 ≤ {x}`.

**Du**: Damit krieg ich die Fälle `0 ≤ {x}` und `{x} < 0`?

**Robo**: Genau! Oder präziser `0 ≤ {x}` und `¬(0 ≤ {x})`. Das ist nicht ganz das gleiche, und man
könnte mit dem Lemma `not_le` zwischen `¬(0 ≤ {x})` und `0 < {x}` wechseln.
"

Hint (x : ℚ) (h : 0 ≤ x) : f (g x) = g (f x) =>
"
**Robo**: Um das ausrechnen zu können, brauchst du nicht nur `0 ≤ x` sondern auch noch
eine neue Annahme `0 ≤ f x`.

**Du**: Also `have h₂ : _`?
"

Hint (x : ℚ) (h : 0 ≤ x) (h₂ : 0 ≤ f x) : f (g x) = g (f x) =>
"
**Du**: Mit den beiden Annahmen sagt die Definition von `g` ja z.B.
`(if 0 ≤ x then _)` wobei ich weiss dass `0 ≤ x` wahr ist,
kann ich das dann einfach vereinfachen?

**Robo**: Dafür must du zuerst die Definition von `g` öffnen, also `unfold`. Und dann mit
dem Lemma `if_pos {h}` das umschreiben.
"

Hint (x : ℚ) (h : ¬ 0 ≤ x) : f (g x) = g (f x) =>
"
**Du**: Ich sehe, das ist jetzt der zweite Fall, da brauch ich sicher wieder eine zweite Annahme
`¬(0 ≤ f x)`…
"

Hint (x : ℚ) (h : ¬ 0 ≤ x) (h₂ : ¬ 0 ≤ f x) : f (g x) = g (f x) =>
"
**Robo**: Jetzt ist der Zeitpunkt wo die Definition von `g` geöffnet sein sollte.

**Robo**: Wenn man ein If-Statement mit wahrer Prämisse mit `if_pos` vereinfacht, dann
braucht man für eine falsche Prämisse…

**Du**: `if_neg`?
"
-- END TODO
HiddenHint (x : ℚ) (h : 0 ≤ x) (h₂ : 0 ≤ f x) : f (2 * x) = g (f x) =>
"
**Robo**: Jetzt das Gleiche noch mit `if_pos {h₂}`.
"

HiddenHint (x : ℚ) (h : 0 ≤ x) (h₂ : 0 ≤ f x) : f (g x) = 2 * f x =>
"
**Robo**: Jetzt das Gleiche noch mit `if_pos {h}`.
"

Hint (x : ℚ) (h : 0 ≤ x) (h₂ : 0 ≤ f x) : f (2 * x) = 2 * f x =>
"
**Robo**: Wenn du jetzt noch die Definition von `f` öffnest, dann kann `ring` den
Rest ausrechnen.
"


-- TODO: This are also showing in the case of the Hint below
-- Proof of `0 ≤ f x`.
Hint (x : ℚ) (h : 0 ≤ x) : 0 ≤ f x =>
" **Robo**: Wenn du die Definition von `f` öffnest, dann hast du schon das wissen,
um das zu beweisen."
HiddenHint (x : ℚ) (h : 0 ≤ x) : 0 ≤ f x =>
"**Du** *(in Gedanken)*: Was war das nochmals... Ungleichungen... `linarith`!"

HiddenHint (x : ℚ) (h : ¬0 ≤ x) : ¬ 0 ≤ f x =>
" **Robo**: Das ist das selbe wie vorhin…"


-- Hint for modifying `h` wrongly.
Hint (x : ℚ) (h : x < 0) : f (g x) = g (f x) =>
"
**Robo**: Das war nicht so ideal, hier brauchst du die Annahme in der Form `({h} : ¬ 0 ≤ {x})`!
"

-- TODO: In this case we get to see the Hints above
Hint (x : ℚ) (h : 0 ≤ x) : 0 ≤ x =>
"**Robo**: Dieses Goal ist entstanden, als du `rw [if_pos]` anstatt `rw [if_pos {h}]`
geschrieben hast."

Hint (x : ℚ) (h : 0 ≤ f x) : 0 ≤ f x =>
"**Robo**: Dieses Goal ist entstanden, als du `rw [if_pos]` anstatt `rw [if_pos {h}]`
geschrieben hast."

Hint (x : ℚ) (h : ¬ 0 ≤ x) : ¬ 0 ≤ x =>
"**Robo**: Dieses Goal ist entstanden, als du `rw [if_neg]` anstatt `rw [if_neg {h}]`
geschrieben hast."

Hint (x : ℚ) (h : ¬ 0 ≤ f x) : ¬ 0 ≤ f x =>
"**Robo**: Dieses Goal ist entstanden, als du `rw [if_neg]` anstatt `rw [if_neg {h}]`
geschrieben hast."

Conclusion
"Zufrieden tauschen die beiden Wächter ihren Platz und geben so dabei den
Durchgang frei."

end LevelFunction4
