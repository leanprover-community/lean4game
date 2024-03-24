/**
 * @fileOverview
*/
import * as React from 'react'
import { Trans, useTranslation } from 'react-i18next'

/** Pop-up that is displayed when opening the help explaining the game rules.
 *
 * `handleClose` is the function to close it again because it's open/closed state is
 * controlled by the containing element.
 */
export function RulesHelpPopup ({handleClose}: {handleClose: () => void}) {
  const { t, i18n } = useTranslation()

  return <div className="privacy-policy modal-wrapper">
  <div className="modal-backdrop" onClick={handleClose} />
  <div className="modal">
    <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
    <h2>{t("Game Rules")}</h2>
    <Trans>
      <p>
        Game rules determine if it is allowed to skip levels and if the games runs checks to only
        allow unlocked tactics and theorems in proofs.
      </p>
      <p>
        Note: "Unlocked" tactics (or theorems) are determined by two things: The set of minimal
        tactics needed to solve a level, plus any tactics you unlocked in another level. That means
        if you unlock <code>simp</code> in a level, you can use it henceforth in any level.
      </p>
      <p>The options are:</p>
    </Trans>
    <table>
      <thead>
        <tr>
          <th scope="col"></th>
          <th scope="col">{t("levels")}</th>
          <th scope="col">{t("tactics")}</th>
        </tr>
      </thead>
      <tbody>
        <tr>
          <th scope="row">{t("regular")}</th>
          <td>🔐</td>
          <td>🔐</td>
        </tr>
        <tr>
          <th scope="row">{t("relaxed")}</th>
          <td>🔓</td>
          <td>🔐</td>
        </tr>
        <tr>
          <th scope="row">{t("none")}</th>
          <td>🔓</td>
          <td>🔓</td>
        </tr>
      </tbody>
    </table>
  </div>
</div>
}
