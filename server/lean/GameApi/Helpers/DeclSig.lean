import Lean

namespace GameServer

open Lean Meta Elab Parser Command

/-- Is the statement a `theorem` or a `def` -/
def declSig.isProp (sig: TSyntax ``declSig) : CommandElabM Bool := do
  let (binders, typeStx) := expandDeclSig sig
  runTermElabM fun _ => do
    Term.elabBinders binders.getArgs fun _ => do
      let statement ← Term.elabType typeStx
      let type ← inferType statement
      return type.isProp

/-- Manual repacking of `declSig` into `optDeclSig`. -/
def declSig.toOptDeclSig (sig: TSyntax ``declSig): TSyntax ``optDeclSig :=
  match sig.raw with
  | .node info ``declSig #[binders, typeStx] =>
    let optType : TSyntax `optType := ⟨Syntax.node info ``Lean.Parser.Term.optType #[typeStx]⟩
    ⟨.node info ``optDeclSig #[binders, optType]⟩
  | _ => unreachable!
