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

Um eine anonyme Funktion `fun x ↦ 1 / (1 + x^2)` innerhalb eines Beweis einem Namen
zuzuordnen, benützt man `let`:

```
let f : ℕ → ℕ := fun (n : ℕ) ↦ n ^ 2
```

Die Taktiken `let` und `have` sind fast gleich, mit einem wichtigen Unterschied. Mit

```
have f : ℕ → ℕ := fun (n : ℕ) ↦ n ^ 2
```

vergisst Lean sofort wie `f` konstruiert wurde, und weiss nur noch dass es eine Funktion
`(f : ℕ → ℕ)` gibt. Mit `let` kann Lean jederzeit auf die Definition von `f` zugreifen.
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

Hint (x : ℤ) : f x = x ^ 2 + 2 * x + 1 =>
"If your function has been defined with a `def` then usually you need to use `unfold f` to
help Lean replacing it with it's definition (alternatively `sim [f]`
oder `rw [f]` funktionieren auch)."
