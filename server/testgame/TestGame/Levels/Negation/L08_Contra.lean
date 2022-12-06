import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose

Game "TestGame"
World "Contradiction"
Level 8

Title "Kontraposition"

Introduction
"
Im Gegensatz zum Widerspruch, wo
"

-- TODO: `even`/`odd` sind in Algebra.Parity. Not ported yet

-- Statement
--   "Ist n² ungerade, so ist auch n ungerade. Beweise durch Widerspruch."
--     (n : ℕ) (h : odd n ^ 2) : odd n := by
--   byContradiction g
--   rw [not_odd] at g
--   ...
--   contradiction

Tactics contradiction
