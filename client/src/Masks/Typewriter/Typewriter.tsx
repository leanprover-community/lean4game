import { faSpinner } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtomValue } from 'jotai'
import { useEffect, useRef } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { InlineConclusion, InlineNextButton } from '../../Chat/Chat'
import { Markdown } from '../../components/Markdown'
import { Toast } from '../../components/Toast'
import { WorldImage } from '../../components/WorldImage'
import { HoverProvider } from '../../GoalView/HoverCode'
import {
  firstStepElement,
  scrollToTop,
  useScrollToSelectedStep,
} from '../../hooks/useStepSelection'
import { gameIdAtom } from '../../state/location-atoms'
import { mobileAtom } from '../../state/preferences-atoms'
import {
  hasError,
  leanInstanceAtom,
  proofCheckAtom,
  solvesGoal,
} from '../../state/proof-atoms'
import { gameInfoAtom, levelInfoAtom } from '../../state/query-atoms'
import { HttpError } from '../../utils/fetch'
import { useGameTranslation } from '../../utils/translation'
import { LeanProgress } from '../LeanProgress'
import { ProofStep } from './ProofStep'
import { proofResultEffect, resetEditingStepEffect } from './typewriter-atoms'
import { typewriterToastAtom } from './typewriter-insert-atoms'
import { TypewriterInput } from './TypewriterInput'

/**
 * The typewriter: the proof steps on top of the world's image, and below them the input
 * line for the next command.
 */
export function Typewriter() {
  const { t } = useTranslation()
  const instance = useAtomValue(leanInstanceAtom)
  const check = useAtomValue(proofCheckAtom)
  const scrollRef = useRef<HTMLDivElement>(null)
  const mobile = useAtomValue(mobileAtom)

  useAtomValue(proofResultEffect)
  useAtomValue(resetEditingStepEffect)
  useScrollToSelectedStep(scrollRef)

  const checkStatus =
    check.error instanceof HttpError ? check.error.status : undefined
  const result = check.data

  // show the last step from its top, i.e. its command, then its hints and goals;
  // without any commands yet, the statement of the level above the initial step
  useEffect(() => {
    const count = result?.steps.length ?? 0
    if (count <= 1) {
      scrollRef.current?.scrollTo({ top: 0 })
      return
    }
    const element = firstStepElement(scrollRef.current, count - 1)
    if (element) scrollToTop(element)
  }, [result])

  const steps = result?.steps ?? []
  const failed = steps.length > 1 && hasError(steps.at(-1))
  const last = steps.at(-1)
  const error = instance.error ?? (checkStatus === 409 ? null : check.error)

  return (
    <div className="relative flex-col h-full bg-(--section-bg) text-left">
      {/* what clicking an insertion button inserted */}
      <Toast messageAtom={typewriterToastAtom} />
      <div className="relative min-h-0 flex-1">
        {/* behind the proof, it does not scroll with it */}
        <WorldImage />
        <div
          ref={scrollRef}
          className="relative flex-col h-full overflow-y-auto"
        >
          <div className="min-h-0 flex-1" />
          <div className="z-1 rounded-t-lg bg-(--bg) px-2 pb-2 shadow-[0_-4px_10px_rgba(0,0,0,0.24)]">
            <ExerciseStatement />
            <HoverProvider
              hovers={result?.hovers ?? []}
              hoverDocs={result?.hoverDocs ?? []}
            >
              {steps.map((step, i) => (
                <ProofStep
                  key={i}
                  step={step}
                  index={i}
                  current={i === steps.length - (failed ? 2 : 1)}
                  failed={failed && i === steps.length - 1}
                  goalSolved={solvesGoal(steps, i)}
                />
              ))}
            </HoverProvider>
            {last && !failed && last.goals.length === 0 && (
              <div
                className={twMerge(
                  'my-2.5 rounded-sm bg-sky-100 px-2.5 py-1.5 text-(--text-h)',
                  'dark:bg-sky-950',
                )}
              >
                {result?.completed ? (
                  <p>{t('typewriter.levelCompleted')}</p>
                ) : (
                  <p>
                    <b>{t('typewriter.noGoalsLeft')}</b>
                    <br />
                    <i>{t('typewriter.noGoalsLeftDescription')}</i>
                  </p>
                )}
              </div>
            )}
            {mobile && <InlineConclusion />}
            {error && (
              <div
                className={twMerge(
                  'my-2.5 rounded-sm border border-error bg-error-bg px-2.5 py-1.5',
                  'text-error',
                )}
              >
                {instance.error
                  ? t('typewriter.startError')
                  : t('typewriter.checkError')}
                <pre className="m-0 text-sm whitespace-pre-wrap">
                  {error.message}
                </pre>
              </div>
            )}
            {!result && !error && (
              <div className="flex-col items-center gap-3 p-4">
                <FontAwesomeIcon
                  icon={faSpinner}
                  spinPulse
                  className="text-3xl text-primary"
                />
                <LeanProgress />
              </div>
            )}
          </div>
        </div>
      </div>
      <TypewriterInput />
      {mobile && <InlineNextButton />}
    </div>
  )
}

/**
 * The statement of the level, e.g. `**Theorem** `name`: description`, followed by its
 * Lean formulation.
 */
function ExerciseStatement() {
  const { t } = useTranslation()
  const gameId = useAtomValue(gameIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const { data: levelInfo } = useAtomValue(levelInfoAtom)
  const { t: gameT } = useGameTranslation(
    gameId ?? '',
    gameInfo?.settings?.allowEmptyTranslations,
  )
  if (!levelInfo?.descrText && !levelInfo?.displayName) return null

  const theorem = levelInfo.displayName
    ? `**${t(
        levelInfo.isProp === false
          ? 'typewriter.definition'
          : 'typewriter.theorem',
      )}** \`${levelInfo.displayName}\`: `
    : ''
  return (
    <div className="px-2 py-4">
      {(levelInfo.descrText || levelInfo.displayName) && (
        <Markdown game={gameId?.replace(/^g\//, '')}>
          {theorem + gameT(levelInfo.descrText ?? '')}
        </Markdown>
      )}
    </div>
  )
}
