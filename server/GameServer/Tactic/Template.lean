import GameServer.Layer.Extension

namespace GameServer

open Lean Elab

/-- A hole inside a template proof that will be replaced by `sorry`. -/
elab (name := GameServer.Tactic.Hole) "Hole" t:tacticSeq : tactic => do
  Tactic.evalTactic t

/--
Iterate recursively through the Syntax, replace `Hole` with `sorry` and remove all
`Hint`/`Branch` occurrences.
-/
def replaceHoles (tacs : Syntax) : Syntax :=
  match tacs with
  | Syntax.node info kind ⟨args⟩ =>
    let newArgs := filterArgs args
    Syntax.node info kind ⟨newArgs⟩
  | other => other
where filterArgs (args : List Syntax) : List Syntax :=
  match args with
    | [] => []
    -- replace `Hole` with `sorry`.
    | Syntax.node info `GameServer.Tactic.Hole _ :: r =>
      Syntax.node info `Lean.Parser.Tactic.tacticSorry #[Syntax.atom info "sorry"] :: filterArgs r
    -- delete all `Hint` and `Branch` occurrences in the middle.
    | Syntax.node _ `GameServer.Tactic.Hint _ :: _ :: r
    | Syntax.node _ `GameServer.Tactic.Branch _ :: _ :: r =>
      filterArgs r
    -- delete `Hint` and `Branch` occurrence at the end of the tactic sequence.
    | Syntax.node _ `GameServer.Tactic.Hint _ :: []
    | Syntax.node _ `GameServer.Tactic.Branch _ :: [] =>
        []
    -- Recurse on all other Syntax.
    | a :: rest =>
      replaceHoles a :: filterArgs rest

/-- The tactic block inside `Template` will be copied into the users editor.
Use `Hole` inside the template for a part of the proof that should be replaced
with `sorry`. -/
elab "Template" tacs:tacticSeq : tactic => do
  Tactic.evalTactic tacs
  let newTacs : TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨replaceHoles tacs.raw⟩
  let template ← PrettyPrinter.ppCategory `Lean.Parser.Tactic.tacticSeq newTacs
  trace[debug] s!"Template:\n{template}"
  modifyLevel (←getCurLevelId) fun level => do
    return {level with template := s!"{template}"}
