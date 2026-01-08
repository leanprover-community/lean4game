import * as React from 'react'
import { Typography } from '@mui/material'
import { Trans, useTranslation } from 'react-i18next'
import { useGetGameInfoQuery } from '../../state/api'
import { GameIdContext } from '../../app'
import { Markdown } from '../markdown'
import { useGameTranslation } from '../../utils/translation'

/** Pop-up that is displaying the Game Info.
 *
 * `handleClose` is the function to close it again because it's open/closed state is
 * controlled by the containing element.
 */
export function InfoPopup () {
  const { t } = useTranslation()
  const gameId = React.useContext(GameIdContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})


  return <>
    <Typography variant="body1" component="div" className="welcome-text">
      <Markdown>{t(gameInfo.data?.info, { ns:gameId })}</Markdown>
      <hr />
      <Trans>
        <h2>{t("Progress saving.translation", { defaultValue: "Progress saving" })}</h2>
        <h2>{t("Progress saving.translation", { defaultValue: "Progress saving" })}</h2>
        <p>
          <Trans
            i18nKey="Progress saving.description"
            defaults="The game stores your progress in your local browser storage. If you delete it, your progress will be lost!<br/>Warning: In most browsers, deleting cookies will also clear the local storage (or 'local site data'). Make sure to download your game progress first!"
          />
          <Trans
            i18nKey="Progress saving.description"
            defaults="The game stores your progress in your local browser storage. If you delete it, your progress will be lost!<br/>Warning: In most browsers, deleting cookies will also clear the local storage (or 'local site data'). Make sure to download your game progress first!"
          />
        </p>
        <h2>{t("Accessibility.translation", { defaultValue: "Accessibility" })}</h2>
        <h2>{t("Accessibility.translation", { defaultValue: "Accessibility" })}</h2>
        <p>
          <Trans
            i18nKey="Accessibility.description"
            defaults="If you experience any accessibilty barriers, please get in contact with us! We are dedicated to address such barriers to the best of our abilities."
          />
          <Trans
            i18nKey="Accessibility.description"
            defaults="If you experience any accessibilty barriers, please get in contact with us! We are dedicated to address such barriers to the best of our abilities."
          />
        </p>
        <h2>{t("Development.translation", { defaultValue: "Development" })}</h2>
        <p>
          <Trans
          i18nKey="Development.description"
          defaults="The game engine has been created by <strong>Alexander Bentkamp</strong>, <strong>Jon Eugster</strong>. On a prototype by <strong>Patrick Massot</strong>. The source code of this Lean game engine is <1>available on Github</1>. If you experience any problems, please file an <2>Issue on Github</2> or get directly in contact."
          components={{
            1: <a target="_blank" href="https://github.com/leanprover-community/lean4game"/>,
            2: <a target="_blank" href="https://github.com/leanprover-community/lean4game/issues"/>
          }}
          />
        </p>
        <h2>{t("Funding.translation", { defaultValue: "Funding" })}</h2>
        <p>
          <Trans
            i18nKey="Funding.description"
            defaults="This server is hosted at Heinrich Heine University Düsseldorf. The lean4game software was developed as part of the project <1>ADAM: Anticipating the Digital Age of Mathematics</1>, funded by the programme <i>Freiraum 2022</i> of the <i>Stiftung Innovation in der Hochschullehre</i>. Ongoing maintenance and development are generously supported by <i>Renaissance Philanthropy</i> through the <i>AI for Math Fund</i>."
            components={{1: <a target="_blank" href="https://hhu-adam.github.io"/>}}
          />
        </p>
      </Trans>
    </Typography>
  </>
}
