/**
 * @fileOverview
*/
import * as React from 'react'
import { Typography } from '@mui/material'
import { Markdown } from '../markdown'
import { useTranslation } from 'react-i18next'
import { GameIdContext } from '../../app'

/** Pop-up that is displaying the Game Info.
 *
 * `handleClose` is the function to close it again because it's open/closed state is
 * controlled by the containing element.
 */
export function InfoPopup ({info, handleClose}: {info: string, handleClose: () => void}) {
  let { t } = useTranslation()
  const gameId = React.useContext(GameIdContext)

  return <div className="modal-wrapper">
  <div className="modal-backdrop" onClick={handleClose} />
  <div className="modal">
    <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
    <Typography variant="body1" component="div" className="welcome-text">
      <Markdown>{t(info, {ns: gameId})}</Markdown>
    </Typography>
  </div>
</div>
}
