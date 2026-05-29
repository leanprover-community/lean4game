import { useTranslation } from "react-i18next"
import { GameHint, ProofState } from "../../../../api/rpc_api"
import React from "react"
import { Button } from "@mui/material"
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome"
import { faDeleteLeft } from "@fortawesome/free-solid-svg-icons"
import { filterHints } from "../../../hints"
import { deletedChatAtom, helpAtom } from "../../../../store/chat-atoms"
import { useAtom } from "jotai"
import { editor } from 'monaco-editor'
import { codeAtom, deleteCodeFromLineAtom, lastProofStepHasErrorsAtom } from "../../../../store/editor-atoms"

//FIXME: implement
function isLastStepWithErrors(x: any, y: any) {
  return false
}

/** The display of a single entered lean command */
export function Command({ proof, i }: { proof: ProofState, i: number }) {
  let {t} = useTranslation()
  const [lastProofStepHasErrors,] = useAtom(lastProofStepHasErrorsAtom)
  const [, setDeletedChat] = useAtom(deletedChatAtom)
  const [help, setHelp] = useAtom(helpAtom)
  const [, setCode] = useAtom(codeAtom)
  const [, deleteCodeFromLine] = useAtom(deleteCodeFromLineAtom)

  // The first step will always have an empty command
  if (!proof.steps[i]?.command) { return <></> }

  //if (isLastStepWithErrors(proof, i))
  if (lastProofStepHasErrors){
    // If the last step has errors, we display the command in a different style
    // indicating that it will be removed on the next try.
    return <div className="failed-command">
      <i>{t("Failed command")}</i>: {proof.steps[i].command}
    </div>
  } else {
    return <div className="command">
      <div className="command-text">{proof.steps[i].command}</div>
      <Button className="undo-button btn btn-inverted" title={t("Retry proof from here")} onClick={ev => {
        deleteCodeFromLine(i)
        ev.stopPropagation()
      }}>
        <FontAwesomeIcon icon={faDeleteLeft} />&nbsp;{t("Retry")}
      </Button>
    </div>
  }
}
