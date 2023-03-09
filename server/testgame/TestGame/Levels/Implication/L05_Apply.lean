import TestGame.Metadata

Game "TestGame"
World "Implication"
Level 5

Title "Implikation"

Introduction
"
Selbstsicher folgt ihr den Anweisungen und geht nach draussen zum
defekten Kontrollelement. Dieses zeigt ein kompliziertes Diagram:
$$
\\begin{CD}
  A  @>{f}>> B       @<{g}<< C       \\\\
  @. @V{h}VV @V{m}VV \\\\
  D  @>{i}>> E       @>{k}>> F       \\\\
  @A{m}AA @A{n}AA @V{p}VV \\\\
  G  @<{q}<< H       @>{r}>> I
\\end{CD}
$$
"

Statement
    "Beweise $A \\Rightarrow F$."
    (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : B → E) (i : D → E) (k : E → F) (m : G → D)
    (n : H → E) (p : F → I) (q : H → G) (r : H → I) : A → I := by
  intro ha
  apply p
  apply k
  apply h
  apply f
  assumption

Hint (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : B → E) (i : D → E) (k : E → F) (m : G → D)
    (n : H → E) (p : F → I) (q : H → G) (r : H → I)  : A → I =>
"**Du**: Also ich muss einen Pfad von Implikationen $A \\Rightarrow I$ finden.

**Robo**: Und dann fängst du am besten wieder mit `intro` an."

HiddenHint (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : B → E) (i : D → E) (k : E → F) (m : G → D)
    (n : H → E) (p : F → I) (q : H → G) (r : H → I) (a : A) : I =>
"**Robo**: Na wieder `apply`, was sonst."

-- TODO: Dieser wird falscherweise bei `F` angezeigt
Hint (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : B → E) (i : D → E) (k : E → F) (m : G → D)
    (n : H → E) (p : F → I) (q : H → G) (r : H → I) (a : A) : H =>
"**Robo**: Das sieht nach einer Sackgasse aus…"

Hint (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : B → E) (i : D → E) (k : E → F) (m : G → D)
    (n : H → E) (p : F → I) (q : H → G) (r : H → I) (a : A) : C =>
"**Robo**: Nah, da stimmt doch was nicht…"

DisabledTactic tauto

Conclusion
"Mit einem lauten Ratteln springen die Förderbänder wieder an."

-- https://www.jmilne.org/not/Mamscd.pdf
