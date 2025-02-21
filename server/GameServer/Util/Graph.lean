import Lean

open Lean Meta

/-!
## Graph

This file provides a directed graph `Graph α β`, which works with keys of type `α` and each
node of the graph has an object of type `β` attached to it.

The keys need to be hashable, but the values from `β` do not need to be.
-/

/--
A (directed) `Graph` consists of notes and edges between these notes.

The edges work on keys (of type `α`) and each note has a value (of type `β`) attached
to this key in order to allow graphs with non-hashable values.
-/
structure Graph (α β : Type _) [BEq α] [Hashable α] where
  nodes: Std.HashMap α β := ∅
  edges: Std.HashSet (α × α) := ∅
deriving Inhabited

variable [BEq α] [Hashable α]

instance : EmptyCollection (Graph α β) := ⟨default⟩

instance [ToString α] [ToJson α] [ToJson β] : ToJson (Graph α β) where
  toJson graph := Json.mkObj [
    ("nodes", Json.mkObj <| graph.nodes.toList.map fun (key, value) => (s!"{key}", toJson value)),
    ("edges", toJson graph.edges.toList)]

-- TODO: Just a dummy implementation for now
instance : FromJson (Graph Name β) where
  fromJson? _ := .ok {
    nodes := ∅
    edges := ∅}

/--
Insert a node with no edges to or from it. Replaces an existing node.
-/
def Graph.insertNode (graph : Graph α β) (a : α) (b : β) : Graph α β :=
  {graph with nodes := graph.nodes.insert a b}

/--
Find all nodes of the `graph` that have a (transitive) connection to `node`.
The key `node` itself is not included in the result.
-/
partial def Graph.predecessors (graph : Graph α β) (node : α) (acc : Std.HashSet α := ∅) :
    Std.HashSet α := Id.run do
  let mut res : Std.HashSet α := acc
  -- iterate over all direct predecessors
  for (source, _) in (graph.edges.filter (·.2 == node)) do
    if !(res.contains source) then
      res := res.insert source
      res := graph.predecessors source res
  return res
