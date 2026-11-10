import { useAtomValue } from 'jotai'
import { type ReactNode } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { hintText, splitIntro, useChatTranslation } from '../../Chat/Chat'
import { useLevelHints } from '../../Chat/useLevelHints'
import { Markdown } from '../../components/Markdown'
import { gameIdAtom } from '../../state/location-atoms'
import { mobileAtom } from '../../state/preferences-atoms'
import { hasError, proofCheckAtom } from '../../state/proof-atoms'
import { levelInfoAtom } from '../../state/query-atoms'

/**
 * The kinds of entries: the severities of Lean's messages, and the texts of the game: the
 * level's introduction and conclusion, and the hints
 */
type Kind =
  | 'error'
  | 'warning'
  | 'information'
  | 'introduction'
  | 'hint'
  | 'conclusion'

/** The texts of the game, which are Markdown */
const gameTexts: Kind[] = ['introduction', 'hint', 'conclusion']

/** Lean's severities, see `ApiDiagnostic` */
const kindOfSeverity: Record<number, Kind> = {
  1: 'error',
  2: 'warning',
  3: 'information',
  4: 'information',
}

const kindClass: Record<Kind, string> = {
  error: 'text-red-700 dark:text-red-400',
  warning: 'text-amber-700 dark:text-amber-400',
  information: 'text-sky-700 dark:text-sky-400',
  introduction: 'text-sky-700 dark:text-sky-400',
  hint: 'text-sky-700 dark:text-sky-400',
  conclusion: 'text-green-700 dark:text-green-400',
}

interface Entry {
  kind: Kind
  /** 1-based line of the text field, if the entry belongs to one */
  line?: number
  content: ReactNode
}

/**
 * The lines of the proof which Lean numbers, as indices of the lines of `text`: Lean gets
 * the proof without empty lines, see `proofOfCode`
 */
function proofLines(text: string) {
  return text
    .split('\n')
    .flatMap((line, i) => (line.trim().length > 0 ? [i] : []))
}

/**
 * The messages of the proof check as a compact transcript below the proof, with the line
 * they belong to. On mobile, where there is no chat, it also contains the chat's
 * messages: the level's introduction, the hints, and the conclusion once the level is
 * completed. Hidden hints are only there if they were revealed in the chat before. Like
 * the typewriter, it says when the level is completed.
 */
export function Transcript({ text }: { text: string }) {
  const { t } = useTranslation()
  const gameT = useChatTranslation()
  const gameId = useAtomValue(gameIdAtom)
  const mobile = useAtomValue(mobileAtom)
  const check = useAtomValue(proofCheckAtom)
  const { hints, completed } = useLevelHints()
  const { data: levelInfo } = useAtomValue(levelInfoAtom)
  const game = gameId?.replace(/^g\//, '')
  /** The paragraphs of an introduction or conclusion as entries */
  const paragraphs = (kind: Kind, gameText: string | null | undefined) =>
    splitIntro(gameT(gameText ?? '')).map(part => ({
      kind,
      content: <Markdown game={game}>{part}</Markdown>,
    }))

  const lines = proofLines(text)
  const textLine = (proofLine: number) => {
    const i = lines[proofLine] as number | undefined
    return i === undefined ? undefined : i + 1
  }

  const steps = check.data?.steps ?? []
  // the first line of each step's tactic in the proof, the initial state has none
  const stepStarts: (number | undefined)[] = []
  let next = 0
  for (const step of steps) {
    if (step.tactic.length === 0) {
      stepStarts.push(undefined)
      continue
    }
    stepStarts.push(next)
    next += step.tactic.split('\n').length
  }

  const entries: Entry[] = []
  if (mobile)
    entries.push(...paragraphs('introduction', levelInfo?.introduction))
  entries.push(
    ...steps.flatMap((step, i) => [
      ...step.diagnostics
        .filter(d => d.message.trim().length > 0)
        .map(d => ({
          kind: kindOfSeverity[d.severity] ?? 'information',
          line: textLine(d.line),
          content: d.message,
        })),
      ...(mobile ? (hints[i] ?? []) : []).map(hint => {
        const start = stepStarts[i]
        return {
          kind: 'hint' as const,
          line: start === undefined ? undefined : textLine(start),
          content: <Markdown game={game}>{hintText(hint, gameT)}</Markdown>,
        }
      }),
    ]),
  )
  // like in the typewriter: whether the level is completed once no goals are left
  const last = steps.at(-1)
  const failed = steps.length > 1 && hasError(last)
  if (last && !failed && last.goals.length === 0) {
    entries.push(
      check.data?.completed
        ? { kind: 'conclusion', content: t('typewriter.levelCompleted') }
        : {
            kind: 'information',
            content: `${t('typewriter.noGoalsLeft')}: ${t('typewriter.noGoalsLeftDescription')}`,
          },
    )
  }
  if (mobile && completed) {
    entries.push(...paragraphs('conclusion', levelInfo?.conclusion))
  }
  if (check.error) {
    entries.push({ kind: 'error', content: check.error.message })
  }
  if (entries.length === 0) return null

  return (
    // grows like the proof, see `Raw`. Without padding, which would count on top of it.
    <div className="mt-3 flex-col max-h-max min-h-0 flex-[1_1_0]">
      <div
        role="log"
        aria-label={t('masks.transcript')}
        className={twMerge(
          'grid min-h-0 grid-cols-[auto_1fr] content-start gap-x-3 gap-y-1',
          'overflow-y-auto rounded-sm bg-(--section-bg) p-2.5 font-mono text-sm',
          // the result of an older proof while the current one is checked
          check.isPlaceholderData && 'opacity-60',
        )}
      >
        {entries.map((entry, i) => (
          <div key={i} className="contents">
            <span className="text-right text-(--text) select-none">
              {entry.line !== undefined && (
                <>
                  <span className="sr-only">
                    {t('masks.line', { line: entry.line })}
                  </span>
                  <span aria-hidden>{entry.line}</span>
                </>
              )}
            </span>
            <div
              className={twMerge(
                'min-w-0 wrap-break-word whitespace-pre-wrap',
                kindClass[entry.kind],
                gameTexts.includes(entry.kind) && 'font-sans whitespace-normal',
              )}
            >
              <span className="sr-only">
                {t(`masks.kinds.${entry.kind}`)}:{' '}
              </span>
              {entry.content}
            </div>
          </div>
        ))}
      </div>
    </div>
  )
}
