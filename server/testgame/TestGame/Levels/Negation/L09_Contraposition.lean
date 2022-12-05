import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose

Game "TestGame"
World "Contradiction"
Level 9

Title "Kontraposition"

Introduction
"
Im Gegensatz zum Widerspruch, wo
"

-- TODO: `even`/`odd` sind in Algebra.Parity. Not ported yet

-- Statement
--   "Ist n² ungerade, so ist auch n ungerade. Beweise durch Kontraposition."
--     (n : ℕ) (h : odd n ^ 2) : odd n := by
--   revert h
--   contrapose
--   rw [not_odd]
--   intro
--   trivial (?)

Tactics contradiction
