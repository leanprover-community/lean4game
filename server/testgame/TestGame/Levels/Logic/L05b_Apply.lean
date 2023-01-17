import TestGame.Metadata

Game "TestGame"
World "Implication"
Level 4

Title "Implikation"

Introduction
"
Angenommen man hat folgende Implikationen
$$
\\begin{CD}
  A  @>{f}>> B       @<{g}<< C       \\\\
  @. @V{h}VV @V{m}VV \\\\
  D  @>{i}>> E       @>{k}>> F
\\end{CD}
$$
und weiss, dass Aussage $A$ wahr ist.
"

Statement
    "Beweise Aussage $F$."
    (A B C D E F : Prop) (hA : A) (f : A → B) (g : C → B) (h : B → E)
     (i : D → E) (k : E → F) (m : C → F) : F := by
  apply k
  apply h
  apply f
  assumption

Hint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (E : Prop) (F : Prop)
    (hA : A) (f : A → B) (g : C → B) (h : B → E)
    (i : D → E) (k : E → F) (m : C → F) : F =>
"Versuch mit `apply` den richtigen Weg zu finden."

Message (A : Prop) (B : Prop) (C : Prop) (D : Prop) (E : Prop) (F : Prop)
    (hA : A) (f : A → B) (g : C → B) (h : B → E)
    (i : D → E) (k : E → F) (m : C → F) : C =>
"Sackgasse. Probier doch einen anderen Weg."

Message (A : Prop) (B : Prop) (C : Prop) (D : Prop) (E : Prop) (F : Prop)
    (hA : A) (f : A → B) (g : C → B) (h : B → E)
    (i : D → E) (k : E → F) (m : C → F) : D =>
"Sackgasse. Probier doch einen anderen Weg."

Tactics apply assumption

-- https://www.jmilne.org/not/Mamscd.pdf
