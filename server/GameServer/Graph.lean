import Lean
import Std.Data.HashMap.Basic

namespace GameServer

open Lean Std

/-! ## Graph -/

variable [inst : BEq α] [inst : Hashable α]

structure Graph (α β : Type) [inst : BEq α] [inst : Hashable α] where
  nodes: HashMap α β := {}
  edges: Array (α × α) := {}
deriving Inhabited

instance [ToJson β] : ToJson (Graph Name β) := {
  toJson := fun graph => Json.mkObj [
    ("nodes", Json.mkObj (graph.nodes.toList.map fun (a,b) => (a.toString, toJson b))),
    ("edges", toJson graph.edges)
  ]
}

-- Just a dummy implementation for now:
instance : FromJson (Graph Name β) := {
  fromJson? := fun _ => .ok {
    nodes := {}
    edges := {}
  }
}

instance  : EmptyCollection (Graph α β) := ⟨default⟩

def Graph.insertNode (g : Graph α β) (a : α) (b : β) :=
  {g with nodes := g.nodes.insert a b}

partial def Graph.predecessors (g : Graph α β) (x : α) (acc : HashSet α := {}) : HashSet α := Id.run do
  let mut res := acc
  let directPredecessors := (g.edges.filter (·.2 == x)).map (·.1)
  for y in directPredecessors do
    if ¬ res.contains y then
      res := res.insert y
      res := g.predecessors y res

  return res
