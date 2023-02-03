import Lean

open Lean Meta

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

instance  : EmptyCollection (Graph α β) := ⟨default⟩

def Graph.insertNode (g : Graph α β) (a : α) (b : β) :=
  {g with nodes := g.nodes.insert a b}

/-- Check if graph contains loops -/
partial def Graph.hasLoops (g : Graph α β) (visited0 : HashSet α := {}): Bool := Id.run do
  let mut visited : HashSet α := visited0
  let all : Array α := g.nodes.toArray.map (·.1)

  -- find some node that we haven't visited
  let some x := all.find? fun x => ¬ visited.contains x
    | return false -- We have visted all nodes and found no loops
  visited := visited.insert x

  match visitSuccessors x x visited with -- visit all recursive successors of x
  | some visited' => visited := visited'
  | none => return true -- none means a loop has been found

  g.hasLoops visited -- continue looking for unvisited nodes

where
  visitSuccessors (x : α) (x0 : α) (visited0 : HashSet α) : Option (HashSet α) := Id.run do
    let mut visited : HashSet α := visited0

    let directSuccessors := (g.edges.filter (·.1 == x)).map (·.2)
    for y in directSuccessors do
      if y == x0 then
        return none -- loop found
      if visited.contains y then
        continue -- no loop possible here because the visited nodes do not lead to x0
      visited := visited.insert y
      match visitSuccessors y x0 visited with
      | some visited' => visited := visited'
      | none => return none

    return some visited

-- #eval Graph.hasLoops ⟨HashMap.ofList [(2,2), (1,1)], #[(2,1)]⟩

partial def Graph.predecessors (g : Graph α β) (x : α) (acc : HashSet α := {}) : HashSet α := Id.run do
  let mut res := acc
  let directPredecessors := (g.edges.filter (·.2 == x)).map (·.1)
  for y in directPredecessors do
    if ¬ res.contains y then
      res := res.insert y
      res := g.predecessors y res

  return res
