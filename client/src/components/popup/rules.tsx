import { Box, Slider } from '@mui/material'
import * as React from 'react'
import { Trans, useTranslation } from 'react-i18next'
import { GameIdContext } from '../../app'
import { changedDifficulty, selectDifficulty } from '../../state/progress'
import { useSelector } from 'react-redux'
import { useContext } from 'react'
import { useAppDispatch } from '../../hooks'

/** Pop-up that is displayed when opening the help explaining the game rules.
 *
 */
export function RulesPopup () {
  const { t } = useTranslation()
  const { gameId } = useContext(GameIdContext)
  const difficulty = useSelector(selectDifficulty(gameId))
  const dispatch = useAppDispatch()

  function label(x : number) {
    return x == 0 ? t("none") : x == 1 ? t("relaxed") : t("regular")
  }

  return <>
    <h2>{t("Game Rules")}</h2>

    {/* <span className="difficulty-label">{t("Rules")}
        <FontAwesomeIcon icon={rulesHelp ? faXmark : faCircleQuestion} className='helpButton' onClick={() => (setRulesHelp(!rulesHelp))}/>
      </span> */}
      <Box className="slider-wrapper">
      <Slider
        orientation="horizontal"
        title={t("Game Rules")}
        min={0} max={2}
        aria-label={t("Game Rules")}
        value={difficulty}
        marks={[
          {value: 0, label: label(0)},
          {value: 1, label: label(1)},
          {value: 2, label: label(2)}
        ]}
        valueLabelFormat={label}
        getAriaValueText={label}
        valueLabelDisplay="off"
        onChange={(ev, val: number) => {
          dispatch(changedDifficulty({game: gameId, difficulty: val}))
        }}
        />
        </Box>
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
  </>
}
