import NNG.Levels.Addition.Level_6

namespace MyNat
open MyNat

axiom succ_inj {a b : ℕ} : succ a = succ b → a = b

axiom zero_ne_succ (a : ℕ) : zero ≠ succ a

axiom add_right_cancel (a t b : ℕ) : a + t = b + t → a = b

axiom add_left_cancel (a b c : ℕ) : a + b = a + c → b = c

