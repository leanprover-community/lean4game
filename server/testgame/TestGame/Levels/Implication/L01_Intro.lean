import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Implication"
Level 1

Title "Intro"

Introduction
"
## Implikationen

In diesem Kapitel lernst du Implikation ($\\Rightarrow$) und Genau-dann-wenn
($\\Leftrightarrow$) kennen.
Dazu lernst du, wie man bereits bewiesene Sätze verwendet.

Seien `(A B : Prop)` zwei logische Aussagen. Eine Implikation $A \\Rightarrow B$ schreibt
man in Lean als `A → B` (`\\to`).

Wenn das Goal eine Implikation $A \\Rightarrow B$ ist, kann man mit
`intro ha` annehmen, dass $A$ wahr ist. Dann muss man $B$ beweisen.
"

Statement
    "Wenn $B$ wahr ist, dann ist die Implikation $A \\Rightarrow (A ∧ B)$ wahr."
    (A B : Prop) (hb : B) : A → (A ∧ B) := by
  intro hA
  constructor
  assumption
  assumption

HiddenHint (A : Prop) (B : Prop) (hb : B) : A → (A ∧ B) =>
"Mit `intro ha` kann man annehmen, dass $A$ wahr ist. danach muss man $A \\land B$ zeigen."

Hint (A : Prop) (B : Prop) (ha : A) (hb : B) : (A ∧ B) =>
"Jetzt kannst du die Taktiken aus dem letzten Kapitel verwenden."

NewTactics intro constructor assumption
