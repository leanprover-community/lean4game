import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Function"
Level 9
Title ""

open MyNat

Introduction
"

"

Statement
""
    (A B C D E F G H I J K L : Type)
    (f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
    (f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
    (f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L) : A → L := by
  intro a
  apply f15
  apply f11
  apply f9
  apply f8
  apply f5
  apply f2
  apply f1
  exact a


Conclusion
"

"
