import Lean.Server.FileWorker.WidgetRequests

/-!
# Hover Information

Encoding interactive Goals with the relevant hover information.

# Implementation notes

For simplicity we calculate all possible hovers eagerly and send them in the `check` response.

Alternatively, one could think about lazily requesting them via RPC. This is what Lean's infoview does,
but it does mean we do have to keep track of an open RPC and send periodic keep-alives. Since we
do not expect game proofs to be too long, we opted for the simpler method and accept the slight
overhead in response size.

The eager loading does not allow for recursive hovers on terms inside of hover popups, but
we do not want them in teh game UI anyways.
-/

open Lean Server Widget Elab

namespace GameServer

/-- Lean's `CodeWithInfos` where each tag is an index into `CheckResult.hovers` -/
abbrev CodeWithHover := TaggedText Nat

/-- The popup shown when hovering over a subexpression. -/
structure Hover where
  /-- The type of the subexpression. -/
  type : Option String
  /-- The subexpression with implicit arguments shown. -/
  expr : Option String
  /-- Index into `CheckResult.docs`. -/
  doc : Option Nat
  deriving FromJson, ToJson

/-- Everything the popup of a subexpression depends on.

Free variables are compared by `FVarId`, so a hypothesis `h` replaced by `rw [..] at h` gets a
different key than the old `h`, while unchanged subterms share their entry across steps. -/
structure HoverKey where
  expr : Expr
  type : Option Expr
  explicit : Bool
  /-- Displayed names of the free variables in `expr`, which may change due to shadowing. -/
  fvarNames : Array Name
  deriving BEq, Hashable

structure HoverTable where
  keys : Std.HashMap HoverKey Nat := {}
  hovers : Array Hover := #[]
  docKeys : Std.HashMap String Nat := {}
  docs : Array String := #[]

abbrev HoverM := StateT HoverTable RequestM

/-- The cache key for a tag, or `none` if its popup should not be cached. -/
def hoverKey? (i : InfoWithCtx) : IO (Option HoverKey) :=
  i.ctx.runMetaM i.info.lctx do
    let (ti, explicit) ← match i.info with
      | .ofTermInfo ti => pure (ti, true)
      -- a custom docstring is a closure which can't be compared
      | .ofDelabTermInfo dti =>
        if dti.mkDocString?.isSome then return none else pure (dti.toTermInfo, dti.explicit)
      | _ => return none
    let expr ← instantiateMVars ti.expr
    let type ← try some <$> (instantiateMVars (← Meta.inferType expr)) catch _ => pure none
    let fvarNames := (collectFVars {} expr).fvarIds.map fun fvarId =>
      (i.info.lctx.find? fvarId).map (·.userName) |>.getD .anonymous
    return some { expr, type, explicit, fvarNames }

def addDoc (doc : String) : HoverM Nat := do
  if let some idx := (← get).docKeys[doc]? then return idx
  modifyGet fun t =>
    (t.docs.size, { t with docKeys := t.docKeys.insert doc t.docs.size, docs := t.docs.push doc })

/-- Compute the popup with Lean's own `makePopup`, without nested hovers. -/
def computeHover (info : WithRpcRef InfoWithCtx) : HoverM Hover := do
  -- `makePopup` is a pure task, so waiting on it doesn't block
  let popup : InfoPopup ← match (← makePopup info).get with
    | .ok popup => pure popup
    | .error e => throw e
  return {
    type := popup.type.map (·.stripTags)
    expr := popup.exprExplicit.map (·.stripTags)
    doc := ← popup.doc.mapM addDoc }

def addHover (info : WithRpcRef InfoWithCtx) : HoverM Nat := do
  let key? ← hoverKey? info.val
  if let some key := key? then
    if let some idx := (← get).keys[key]? then return idx
  let hover ← computeHover info
  modifyGet fun t =>
    let idx := t.hovers.size
    (idx, { t with
      hovers := t.hovers.push hover
      keys := match key? with
        | some key => t.keys.insert key idx
        | none => t.keys })

/-- Replace the tags of the code by indices into the hover table. -/
def encodeWithHover (code : CodeWithInfos) : HoverM CodeWithHover :=
  code.mapM (addHover ·.info)

end GameServer
