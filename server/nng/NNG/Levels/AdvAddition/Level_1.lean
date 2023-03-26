import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvAddition"
Level 1
Title ""

open MyNat

Introduction
"

"

theorem MyNat.succ_inj {a b : ℕ} : succ a = succ b → a = b := by simp only [succ.injEq, imp_self]

theorem MyNat.zero_ne_succ (a : ℕ) : zero ≠ succ a := by simp only [ne_eq, not_false_iff]

Statement succ_inj'
""
    {a b : ℕ} (hs : succ a = succ b) :  a = b := by
    exact succ_inj hs

NewLemma MyNat.succ_inj MyNat.zero_ne_succ

Conclusion
"

"
