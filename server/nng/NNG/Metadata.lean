import GameServer.Commands

import NNG.MyNat.Definition

import NNG.Doc.Definitions
import NNG.Doc.Lemmas
import NNG.Doc.Tactics

import NNG.Tactic.Induction
import NNG.Tactic.Rfl
import NNG.Tactic.Rw
import Std.Tactic.RCases
import Mathlib.Tactic.Have
import Mathlib.Tactic.LeftRight

-- TODO: Why does this not work here??
-- We do not want `simp` to be able to do anything unless we unlock it manually.
attribute [-simp] MyNat.succ.injEq