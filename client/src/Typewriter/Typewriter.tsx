import { faSpinner } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtom, useAtomValue, useSetAtom } from 'jotai'
import { useEffect, useRef } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { Markdown } from '../components/Markdown'
import { gameIdAtom, levelIdAtom, worldIdAtom } from '../state/location-atoms'
import { completedAtom } from '../state/progress-atoms'
import {
  editingStepAtom,
  hasError,
  leanInstanceAtom,
  proofCheckAtom,
} from '../state/proof-atoms'
import { gameInfoAtom, levelInfoAtom } from '../state/query-atoms'
import { HttpError, gameDataUrl } from '../utils/fetch'
import { useGameTranslation } from '../utils/translation'
import { HoverProvider } from './HoverCode'
import { ProofStep } from './ProofStep'
import { TypewriterInput } from './TypewriterInput'

/** Time between keepalives of the Lean instance, the server stops it after 5 idle minutes */
const KEEPALIVE_MS = 60_000

/**
 * The typewriter: the proof steps on top of the level's image, and below them the input
 * line for the next command.
 */
export function Typewriter() {
  const { t } = useTranslation()
  const gameId = useAtomValue(gameIdAtom)
  const { data: levelInfo } = useAtomValue(levelInfoAtom)
  const instance = useAtomValue(leanInstanceAtom)
  const check = useAtomValue(proofCheckAtom)
  const [completed, setCompleted] = useAtom(completedAtom)
  const scrollRef = useRef<HTMLDivElement>(null)

  useLeanKeepalive()

  // stop editing a step when going to another level
  const worldId = useAtomValue(worldIdAtom)
  const levelId = useAtomValue(levelIdAtom)
  const setEditingStep = useSetAtom(editingStepAtom)
  useEffect(() => setEditingStep(null), [worldId, levelId, setEditingStep])

  // the instance is gone, e.g. stopped after being idle
  const { refetch: restartInstance } = instance
  const checkStatus =
    check.error instanceof HttpError ? check.error.status : undefined
  useEffect(() => {
    if (checkStatus === 404) void restartInstance()
  }, [checkStatus, restartInstance])

  const result = check.data
  useEffect(() => {
    if (result?.completed && !completed) setCompleted(true)
  }, [result, completed, setCompleted])

  // show the newest step
  useEffect(() => {
    const scroll = scrollRef.current
    if (scroll) scroll.scrollTop = scroll.scrollHeight
  }, [result])

  const steps = result?.steps ?? []
  const failed = steps.length > 1 && hasError(steps.at(-1))
  const last = steps.at(-1)
  const error = instance.error ?? (checkStatus === 409 ? null : check.error)

  return (
    <div className="flex-col h-full text-left">
      <div
        ref={scrollRef}
        className={twMerge(
          'relative flex-col min-h-0 flex-1 overflow-y-auto',
          'bg-(--section-bg)',
        )}
      >
        {levelInfo?.image && gameId && (
          <img
            className="absolute max-h-full w-full object-contain"
            src={gameDataUrl(gameId, levelInfo.image)}
            alt=""
          />
        )}
        <div className="min-h-0 flex-1" />
        <div className="z-1 rounded-t-lg bg-(--bg) px-2 pb-2">
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
            <div className="flex justify-center p-4 text-3xl text-primary">
              <FontAwesomeIcon icon={faSpinner} spinPulse />
            </div>
          )}
        </div>
      </div>
      <TypewriterInput />
    </div>
  )
}

/** Keeps the Lean instance of the game running, and restarts it if it is gone */
function useLeanKeepalive() {
  const { data, refetch } = useAtomValue(leanInstanceAtom)
  const id = data?.id
  useEffect(() => {
    if (!id) return
    const interval = setInterval(() => {
      void fetch(`/api/lean/instances/${id}/keepalive`, {
        method: 'POST',
      }).then(res => {
        if (res.status === 404) void refetch()
      })
    }, KEEPALIVE_MS)
    return () => clearInterval(interval)
  }, [id, refetch])
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
  if (!levelInfo?.descrText && !levelInfo?.descrFormat) return null
  const theorem = levelInfo.displayName
    ? `**${t('typewriter.theorem')}** \`${levelInfo.displayName}\`: `
    : ''
  return (
    <div className="px-2 py-4">
      {(levelInfo.descrText || levelInfo.displayName) && (
        <Markdown game={gameId?.replace(/^g\//, '')}>
          {theorem + gameT(levelInfo.descrText ?? '')}
        </Markdown>
      )}
      {levelInfo.descrFormat && (
        <p>
          <code className="text-xs">{levelInfo.descrFormat}</code>
        </p>
      )}
    </div>
  )
}
