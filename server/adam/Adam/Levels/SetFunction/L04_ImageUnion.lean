import Adam.Metadata
import Adam.Options.MathlibPart

Game "Adam"
World "SetFunction"
Level 4

Title ""

Introduction
"
Wenn man Aussagen über Familien von Mengen machen will, macht man das mit
`(N : I → Set V)`, also also Funktionen von einer Indexmenge.
"

Statement
""
    (I U V : Type _) (f : U → V) (N : I → Set V) :
    f ⁻¹' (⋃ (i : I), N i) = ⋃ i, f ⁻¹' (N i) := by
  simp
