import GameServer.CheckProof.CheckProof

/-!
RPC method used by the server's proof check endpoint.

The document is expected to contain a `Runner` command whose tactic block starts at
line `proofStartLine` with one tactic per line. The result contains the proof state
(goals, hypotheses, hints) and the diagnostics after each tactic, all as plain strings
so it can be passed on as JSON without an RPC session.
-/

open Lean.Server RequestM

/-- RPC method to get the proof state after each tactic -/
@[server_rpc_method]
def _root_.Game.checkProof (p : GameServer.CheckProofParams) :
    RequestM (RequestTask GameServer.CheckResult) :=
  GameServer.checkProof p
