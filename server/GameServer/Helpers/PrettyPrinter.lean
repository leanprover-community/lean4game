--import Lean
import Lean.PrettyPrinter.Delaborator.Builtins
import Lean.PrettyPrinter
import Lean

import Std.Tactic.OpenPrivate

namespace GameServer

namespace PrettyPrinter

open Lean Meta
open Lean.Parser Term
open PrettyPrinter Delaborator SubExpr
open TSyntax.Compat


#check Command.declSig

open private shouldGroupWithNext evalSyntaxConstant from Lean.PrettyPrinter.Delaborator.Builtins

-- def typeSpec := leading_parser " :\\n: " >> termParser

-- def declSig := leading_parser
--   many (ppSpace >> (Term.binderIdent <|> Term.bracketedBinder)) >> typeSpec


@[inherit_doc Lean.PrettyPrinter.Delaborator.delabConstWithSignature]
partial def delabConstWithSignature : Delab := do
  let e ← getExpr
  -- use virtual expression node of arity 2 to separate name and type info
  let idStx ← descend e 0 <|
    withOptions (pp.universes.set · true |> (pp.fullNames.set · true)) <|
      delabConst
  descend (← inferType e) 1 <|
    delabParams idStx #[] #[]
where
  -- follows `delabBinders`, but does not uniquify binder names and accumulates all binder groups
  delabParams (idStx : Ident) (groups : TSyntaxArray ``bracketedBinder) (curIds : Array Ident) := do
    if let .forallE n d _ i ← getExpr then
      let stxN ← annotateCurPos (mkIdent n)
      let curIds := curIds.push ⟨stxN⟩
      if ← shouldGroupWithNext then
        withBindingBody n <| delabParams idStx groups curIds
      else
        let delabTy := withOptions (pp.piBinderTypes.set · false) delab
        let group ← withBindingDomain do
          match i with
          | .implicit       => `(bracketedBinderF|{$curIds*})
          | .strictImplicit => `(bracketedBinderF|⦃$curIds*⦄)
          | .instImplicit   => `(bracketedBinderF|[$(← delabTy)])
          | _ =>
            if d.isOptParam then
              `(bracketedBinderF|($curIds* : $(← withAppFn <| withAppArg delabTy) := $(← withAppArg delabTy)))
            else if let some (.const tacticDecl _) := d.getAutoParamTactic? then
              let tacticSyntax ← ofExcept <| evalSyntaxConstant (← getEnv) (← getOptions) tacticDecl
              `(bracketedBinderF|($curIds* : $(← withAppFn <| withAppArg delabTy) := by $tacticSyntax))
            else
              `(bracketedBinderF|($curIds* : $(← delabTy)))
        withBindingBody n <| delabParams idStx (groups.push group) #[]
    else
      let type ← delab

      -- pure type
      `(Command.declSig| $groups* : $type)

@[inherit_doc Lean.PrettyPrinter.ppSignature]
def ppSignature (c : Name) : MetaM FormatWithInfos := do
  let decl ← getConstInfo c
  let e := .const c (decl.levelParams.map mkLevelParam)
  let (stx, infos) ← delabCore e (delab := delabConstWithSignature)
  return ⟨← ppTerm ⟨stx⟩, infos⟩  -- HACK: not a term

end PrettyPrinter

open Lean Meta Elab Command

/-! ## Statement string -/

def getStatement (name : Name) : CommandElabM MessageData := do
  return ← addMessageContextPartial (.ofPPFormat { pp := fun
    | some ctx => ctx.runMetaM <| GameServer.PrettyPrinter.ppSignature name
    | none     => return "that's a bug." })

-- Note: We use `String` because we can't send `MessageData` as json, but
-- `MessageData` might be better for interactive highlighting.
/-- Get a string of the form `my_lemma (n : ℕ) : n + n = 2 * n`.

Note: A statement like `theorem abc : ∀ x : Nat, x ≥ 0` would be turned into
`theorem abc (x : Nat) : x ≥ 0` by `PrettyPrinter.ppSignature`. -/
def getStatementString (name : Name) : CommandElabM String := do
  --try
    return ← (← getStatement name).toString
  --catch
  --| _ => throwError m!"Could not find {name} in context."
  -- TODO: I think it would be nicer to unresolve Namespaces as much as possible.
