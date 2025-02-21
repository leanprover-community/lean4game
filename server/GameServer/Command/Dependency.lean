import GameServer.Layer.Extension

namespace GameServer

open Lean Elab

/-- The worlds of a game are joint by dependencies. These are
automatically computed but can also be defined with the syntax
`Dependency World₁ → World₂ → World₃`. -/
def Parser.dependency := Parser.sepBy1Indent Parser.ident "→"

/-- Manually add a dependency between two worlds.

Normally, the dependencies are computed automatically by the
tactics & theorems used in the example
proof and the ones introduced by `NewTheorem`/`NewTactic`.
Use the command `Dependency World₁ → World₂` to add a manual edge to the graph,
for example if the only dependency between the worlds is given by
the narrative. -/
elab "Dependency" s:Parser.dependency : command => do
  let mut source? : Option Name := none
  for stx in s.raw.getArgs.getEvenElems do
    let some source := source?
      | do
          source? := some stx.getId
          continue
    let target := stx.getId
    match (← getCurGame).worlds.nodes.get? target with
    | some _ => pure ()
    | none => logErrorAt stx m!"World `{target}` seems not to exist"

    modifyCurGame fun game =>
      pure {game with worlds := {game.worlds with edges := game.worlds.edges.insert (source, target)}}
    source? := some target
