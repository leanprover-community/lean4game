import * as React from 'react';
import { useContext, useEffect, useRef, useState } from 'react'
import { useTranslation } from "react-i18next"
import { GameIdContext } from '../../state/context';
import { useLoadLevelQuery } from '../../state/api';
import { Markdown } from '../utils';

/** The mathematical formulation of the statement, supporting e.g. Latex
 * It takes three forms, depending on the precence of name and description:
 * - Theorem xyz: description
 * - Theorem xyz
 * - Exercises: description
 *
 * If `showLeanStatement` is true, it will additionally display the lean code.
 */
export function ExerciseStatement({ showLeanStatement = false }) {
  let { t } = useTranslation()
  const {gameId, worldId, levelId } = useContext(GameIdContext)
  const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})

  if (!(levelInfo.data?.descrText || levelInfo.data?.descrFormat)) { return <></> }
  return <>
    <div className="exercise-statement">
      {levelInfo.data?.descrText ?
        <Markdown>
          {(levelInfo.data?.displayName ? `**${t("Theorem")}** \`${levelInfo.data?.displayName}\`: ` : '') + t(levelInfo.data?.descrText, {ns: gameId})}
        </Markdown> : levelInfo.data?.displayName &&
        <Markdown>
          {`**${t("Theorem")}** \`${levelInfo.data?.displayName}\``}
        </Markdown>
      }
      {levelInfo.data?.descrFormat && showLeanStatement &&
        <p><code className="lean-code">{levelInfo.data?.descrFormat}</code></p>
      }
    </div>
  </>
}
