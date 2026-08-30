import React from "react"
import { useTranslation } from "react-i18next"
import { useGameTranslation } from "../../utils/translation"
import { useAtom } from "jotai"
import { gameIdAtom } from "../../store/location-atoms"
import { levelInfoAtom } from "../../store/query-atoms"
import { Markdown } from "../markdown"

/** The mathematical formulation of the statement, supporting e.g. Latex
 * It takes three forms, depending on the precence of name and description:
 * - Theorem xyz: description
 * - Theorem xyz
 * - Exercises: description
 *
 * If `showLeanStatement` is true, it will additionally display the lean code.
 */
export function ExerciseStatement({ showLeanStatement = false }) {
  const { t : gT } = useGameTranslation()
  const { t } = useTranslation()
  const [gameId] = useAtom(gameIdAtom)
  const [{ data: levelInfo }] = useAtom(levelInfoAtom)

  if (!(levelInfo?.descrText || levelInfo?.descrFormat)) { return <></> }
  return <>
    <div className="exercise-statement">
      {levelInfo?.descrText ?
        <Markdown>
          {(levelInfo?.displayName ? `**${t("Theorem")}** \`${levelInfo?.displayName}\`: ` : '') + t(levelInfo?.descrText, {ns: gameId})}
        </Markdown> : levelInfo?.displayName &&
        <Markdown>
          {(levelInfo?.displayName ? `**${t("Theorem")}** \`${levelInfo?.displayName}\`: ` : '') + gT(levelInfo?.descrText ?? "")}
        </Markdown>
      }
      {levelInfo?.descrFormat && showLeanStatement &&
        <p><code className="lean-code">{levelInfo?.descrFormat}</code></p>
      }
    </div>
  </>
}
