import React, { useContext } from "react"
import { GameIdContext } from "../../app"
import { useLoadDocQuery } from "../../state/api"
import { Markdown } from "../markdown"
import { useTranslation } from "react-i18next"

export function Documentation({name, type, handleClose}) {
  const { t } = useTranslation()
  const gameId = useContext(GameIdContext)
  const doc = useLoadDocQuery({game: gameId, type: type, name: name})

  return <div className="documentation">
    <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
    <h1 className="doc">{doc.data?.displayName}</h1>
    <p><code>{doc.data?.statement}</code></p>
    {/* <code>docstring: {doc.data?.docstring}</code> */}
    <Markdown>{t(doc.data?.content, {ns: gameId})}</Markdown>
  </div>
}
