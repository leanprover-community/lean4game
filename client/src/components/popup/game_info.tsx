/**
 * @fileOverview
*/
import * as React from 'react'
import { Typography } from '@mui/material'
import Markdown from '../markdown'
import { Trans, useTranslation } from 'react-i18next'
import { GameIdContext } from '../../app'
import { useGetGameInfoQuery } from '../../state/api'

/** Pop-up that is displaying the Game Info.
 *
 * `handleClose` is the function to close it again because it's open/closed state is
 * controlled by the containing element.
 */
export function InfoPopup () {
  let { t } = useTranslation()
  const {gameId} = React.useContext(GameIdContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})

  return <>
    <Typography variant="body1" component="div" className="welcome-text">
      <Markdown>{t(gameInfo.data?.info, {ns: gameId})}</Markdown>
      <hr />
      <Trans>
        <h2>Progress saving</h2>
        <p>
          The game stores your progress in your local browser storage. If you delete it, your progress will be lost!<br />
          Warning: In most browsers, deleting cookies will also clear the local storage (or "local site data").
          Make sure to download your game progress first!
        </p>
        <h2>Development</h2>
        <p>The game engine has been created by <strong>Alexander Bentkamp</strong>, <strong>Jon Eugster</strong>.
          On a prototype by <strong>Patrick Massot</strong>.
        </p>
        <p>
          The source code of this Lean game engine
          is <a href="https://github.com/leanprover-community/lean4game" target="_blank">available on Github</a>.
          If you experience any problems, please
          file an <a href="https://github.com/leanprover-community/lean4game/issues" target="_blank">Issue on Github</a> or
          get directly in contact.
        </p>
        <h2>Funding</h2>
        <p>
          The game engine has been developed as part of the
          project <a href="https://hhu-adam.github.io/" target="_blank">ADAM: Anticipating the Digital
          Age of Mathematics</a> at
          Heinrich-Heine-Universität Düsseldorf. It is funded by
          the <i>Stiftung Innovation in der Hochschullehre</i> as part of project <i>Freiraum 2022</i>.
        </p>
      </Trans>
    </Typography>
  </>
}
