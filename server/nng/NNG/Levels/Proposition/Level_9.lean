import NNG.Metadata
import NNG.MyNat.Addition
import NNG.MyNat.Theorems.Proposition

Game "NNG"
World "Proposition"
Level 9
Title ""

open MyNat

Introduction
"

"

Statement
""
    (A B C D E F G H I J K L : Prop)
    (f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
    (f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
    (f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L) : A → L := by
  -- cc -- TODO: `cc` is not ported yet.
  sorry

Conclusion
"

"
