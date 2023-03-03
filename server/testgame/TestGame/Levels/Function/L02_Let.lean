import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 2

Title ""

Introduction
"
Ausserhalb eines Beweises kann man Funktionen mit `def`
(anstatt `lemma`/`example`/`theorem`) definieren:

```
def f (x : ℚ) : ℚ := 1 / (1 + x^2)

def f : ℚ → ℚ := fun x ↦ 1 / (1 + x^2)
```

(die beiden Varianten sind äquivalent.)

Um eine anonyme Funktion `fun x ↦ 1 / (1 + x^2)` **innerhalb** eines Beweis einem Namen
zuzuordnen, benützt man `let`:

```
let f : ℕ → ℕ := fun (n : ℕ) ↦ n ^ 2
```

`def` und `let` funktionieren also fast gleich wie `lemma`/`example`/`theorem` und `have` mit
einem wichtigen Unterschied:

```
have f : ℕ → ℕ := fun (n : ℕ) ↦ n ^ 2
let f₂ : ℕ → ℕ := fun (n : ℕ) ↦ n ^ 2
```

`have` vergisst sofort den \"Beweis\", das heisst, Lean weiss dann nur, dass es eine
Funktion `(f : ℕ → ℕ)` gibt, aber nicht, wie diese definiert ist. `let` hingegen speichert
die Definition der Funktion.

Manchmal muss man Definitionen (von einem `def` oder `let` Statement) mit `unfold` einsetzen.
"

def f (x : ℤ) : ℤ := (x + 1) ^ 2

Statement
"
Given the function
```
def f (x : ℤ) : ℤ := (x + 1) ^ 2
```
show that $f(x) = x^2 + 2x + 1$.

"
    : ∀ x, f x = x ^ 2 + 2 * x + 1 := by
  intro x
  unfold f
  ring

NewTactics «let»
OnlyTactics «let» intro unfold ring

HiddenHint : ∀ x, f x = x ^ 2 + 2 * x + 1 =>
"Fang zuerst wie immer mit `intro x` an."

Hint (x : ℤ) : f x = x ^ 2 + 2 * x + 1 =>
"
Definitionen muss man anundzu manuell einsetzen um den Taktiken zu helfen.

Das macht man mit `unfold f` (oder alternativ mit `rw [f]`).
"

HiddenHint (x : ℤ) : f x = x ^ 2 + 2 * x + 1 =>
"
Nachdem die Definition von `f` eingesetzt ist, übernimmt `ring` den Rest"
