import Lean.Parser.Types
import Lean.Elab.Command

namespace Lean

/-- Add a message. use `(severity := .warning)` to specify the severity. -/
def addMessage (info : SourceInfo) (inputCtx : Parser.InputContext)
    (severity := MessageSeverity.warning) (s : MessageData) :
    Elab.Command.CommandElabM Unit := do
  modify fun st => { st with
    messages := st.messages.add {
      fileName := inputCtx.fileName
      severity := severity
      pos      := inputCtx.fileMap.toPosition (info.getPos?.getD 0)
      data     := s }}
