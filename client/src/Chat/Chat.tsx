import { faArrowRight, faHome } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtomValue, useSetAtom } from 'jotai'
import { type HTMLAttributes, type ReactNode, useEffect, useRef } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import type { ApiHint } from '../api'
import { Button, LinkButton } from '../components/Button'
import { Markdown } from '../components/Markdown'
import { gameCompletedAtom } from '../GamePage/world-tree-atoms'
import {
  useScrollToSelectedStep,
  useStepSelection,
} from '../hooks/useStepSelection'
import { leftPanelOpenAtom } from '../state/layout-atoms'
import {
  gameIdAtom,
  gamePath,
  levelIdAtom,
  worldConclusionPath,
  worldIdAtom,
} from '../state/location-atoms'
import { mobileAtom } from '../state/preferences-atoms'
import { readWorldIntroAtom } from '../state/progress-atoms'
import { editingStepAtom } from '../state/proof-atoms'
import {
  gameInfoAtom,
  levelInfoAtom,
  worldConclusionAtom,
} from '../state/query-atoms'
import { useGameTranslation } from '../utils/translation'
import { readGameIntroAtom } from './chat-atoms'
import { useLevelHints } from './useLevelHints'

export type GameT = (key: string | undefined) => string

/** The translation of the current game's texts */
export function useChatTranslation() {
  const gameId = useAtomValue(gameIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const { t: gameT } = useGameTranslation(
    gameId ?? '',
    gameInfo?.settings?.allowEmptyTranslations,
  )
  return gameT
}

/** Splits an introduction into messages at blank lines */
export function splitIntro(text: string) {
  return text.split(/\n(\s*\n)+/).filter(part => part.trim())
}

/**
 * The translated text of a hint, with the variable names marked like `«{g}»` replaced
 * by the ones the player used
 */
export function hintText(hint: ApiHint, gameT: GameT) {
  // hints created in the frontend do not have a `rawText`
  if (!hint.rawText) return gameT(hint.text)
  return gameT(hint.rawText).replaceAll(
    /«\{(.*?)\}»/g,
    (_, v: string) => hint.varNames.find(x => x[0] === v)?.[1] ?? '',
  )
}

/**
 * The kind of a chat message: `hidden` for revealed hidden hints, and `deleted` for
 * messages of proof steps which are removed once the edited command is executed
 */
type MessageVariant = 'default' | 'hidden' | 'conclusion' | 'deleted'

const variantClass: Record<MessageVariant, string> = {
  default: 'bg-sky-100 text-(--text-h) dark:bg-sky-950',
  hidden: 'bg-amber-100 text-amber-800 dark:bg-amber-950 dark:text-amber-200',
  conclusion: 'bg-green-100 text-(--text-h) dark:bg-green-950',
  deleted: 'bg-gray-100 text-gray-500 dark:bg-gray-800 dark:text-gray-400',
}

type ChatMessageProps = {
  children: string
  variant?: MessageVariant
} & Omit<HTMLAttributes<HTMLDivElement>, 'children'>

/** A message of the chat, colored by its `variant` */
function ChatMessage({
  children,
  variant = 'default',
  className,
  ...props
}: ChatMessageProps) {
  const gameId = useAtomValue(gameIdAtom)
  return (
    <div
      className={twMerge(
        'my-2.5 overflow-x-auto rounded-sm px-2.5 py-1.5',
        variantClass[variant],
        className,
      )}
      {...props}
    >
      <Markdown game={gameId?.replace(/^g\//, '')}>{children}</Markdown>
    </div>
  )
}

/** A message belonging to the proof step `step`, selecting it on focus */
function StepMessage({ step, ...props }: ChatMessageProps & { step: number }) {
  const selection = useStepSelection(step)
  return (
    <ChatMessage
      {...props}
      {...selection.props}
      className={selection.className}
    />
  )
}

/** A row of buttons below a thin line */
function ButtonRow({ children }: { children: ReactNode }) {
  return (
    <div className="flex shrink-0 flex-wrap gap-2 border-t border-(--border) p-2">
      {children}
    </div>
  )
}

/**
 * The chat: the messages, scrolling to the ones of the selected proof step, and below
 * them a row of `buttons`. When `newestKey` changes, it scrolls to the newest message.
 */
function Chat({
  children,
  buttons,
  newestKey,
}: {
  children: ReactNode
  buttons?: ReactNode
  newestKey?: string
}) {
  const ref = useRef<HTMLDivElement>(null)
  useScrollToSelectedStep(ref)
  useEffect(() => {
    const scroll = ref.current
    if (scroll && newestKey !== undefined)
      scroll.scrollTop = scroll.scrollHeight
  }, [newestKey])
  return (
    <div className="flex-col h-full text-left">
      <div ref={ref} className="min-h-0 flex-1 overflow-y-auto px-2">
        {children}
      </div>
      {buttons && <ButtonRow>{buttons}</ButtonRow>}
    </div>
  )
}

/**
 * A button on the right of the row to go on to `href`. While `disabled`, it is a
 * disabled button, as a link cannot be disabled. The link takes the focus when it
 * appears, to go on by pressing enter.
 */
function ForwardButton({
  href,
  disabled = false,
  onClick,
  children,
}: {
  href: string
  disabled?: boolean
  onClick?: () => void
  children: ReactNode
}) {
  const ref = useRef<HTMLAnchorElement>(null)
  useEffect(() => {
    if (!disabled) ref.current?.focus()
  }, [disabled])
  return disabled ? (
    <Button className="ml-auto" disabled>
      {children}
    </Button>
  ) : (
    <LinkButton ref={ref} className="ml-auto" href={href} onClick={onClick}>
      {children}
    </LinkButton>
  )
}

/** Goes to the first level of the world, or home if the world has none */
function StartButton() {
  const { t } = useTranslation()
  const gameId = useAtomValue(gameIdAtom)
  const worldId = useAtomValue(worldIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const readWorldIntro = useSetAtom(readWorldIntroAtom)
  if (gameId === undefined || worldId === undefined) return null
  if (gameInfo?.worldSize?.[worldId] === 0) return <HomeButton />
  return (
    <ForwardButton
      href={gamePath(gameId, worldId, 1)}
      onClick={() => readWorldIntro()}
    >
      {t('appBar.start')}&nbsp;
      <FontAwesomeIcon icon={faArrowRight} />
    </ForwardButton>
  )
}

/** Goes home, to the game overview */
function HomeButton({ disabled = false }: { disabled?: boolean }) {
  const { t } = useTranslation()
  const gameId = useAtomValue(gameIdAtom)
  if (gameId === undefined) return null
  return (
    <ForwardButton href={gamePath(gameId)} disabled={disabled}>
      <FontAwesomeIcon icon={faHome} />
      &nbsp;{t('appBar.home')}
    </ForwardButton>
  )
}

/**
 * Goes to the next level. After the world's last level, it goes to the world's
 * conclusion if it has one, otherwise home.
 */
function NextButton({ disabled }: { disabled: boolean }) {
  const { t } = useTranslation()
  const gameId = useAtomValue(gameIdAtom)
  const worldId = useAtomValue(worldIdAtom)
  const levelId = useAtomValue(levelIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const worldConclusion = useAtomValue(worldConclusionAtom)
  const worldSize =
    worldId === undefined ? undefined : gameInfo?.worldSize?.[worldId]
  if (
    gameId === undefined ||
    worldId === undefined ||
    levelId === undefined ||
    worldSize === undefined
  )
    return null
  if (levelId >= worldSize && !worldConclusion)
    return <HomeButton disabled={disabled} />
  return (
    <ForwardButton
      href={
        levelId >= worldSize
          ? worldConclusionPath(gameId, worldId)
          : gamePath(gameId, worldId, levelId + 1)
      }
      disabled={disabled}
    >
      {t('appBar.next')}&nbsp;
      <FontAwesomeIcon icon={faArrowRight} />
    </ForwardButton>
  )
}

/**
 * An introduction or a conclusion, one message per paragraph. On a level, it belongs to
 * the proof step `step`.
 */
function IntroMessages({
  text,
  step,
  variant,
}: {
  text: string | null | undefined
  step?: number
  variant?: MessageVariant
}) {
  const gameT = useChatTranslation()
  return splitIntro(gameT(text ?? '')).map((part, i) =>
    step === undefined ? (
      <ChatMessage key={i} variant={variant}>
        {part}
      </ChatMessage>
    ) : (
      <StepMessage key={i} step={step} variant={variant}>
        {part}
      </StepMessage>
    ),
  )
}

/**
 * On mobile, where the chat covers the world tree: closes the chat and remembers that
 * the introduction was read, so it is closed from then on
 */
function GameStartButton() {
  const { t } = useTranslation()
  const setReadGameIntro = useSetAtom(readGameIntroAtom)
  const setLeftPanelOpen = useSetAtom(leftPanelOpenAtom)
  return (
    <Button
      className="ml-auto"
      onClick={() => {
        setReadGameIntro(true)
        setLeftPanelOpen(false)
      }}
    >
      {t('appBar.start')}&nbsp;
      <FontAwesomeIcon icon={faArrowRight} />
    </Button>
  )
}

/**
 * The chat on the game overview: the game's introduction, and its conclusion once all
 * worlds are completed
 */
export function GameChat() {
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const mobile = useAtomValue(mobileAtom)
  const gameCompleted = useAtomValue(gameCompletedAtom)
  return (
    <Chat buttons={mobile && <GameStartButton />}>
      <IntroMessages text={gameInfo?.introduction} />
      {gameCompleted && (
        <IntroMessages text={gameInfo?.conclusion} variant="conclusion" />
      )}
    </Chat>
  )
}

/** The chat on a world's page: the world's introduction */
export function WorldChat() {
  const worldId = useAtomValue(worldIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const world =
    worldId === undefined ? undefined : gameInfo?.worlds?.nodes[worldId]
  return (
    <Chat buttons={<StartButton />}>
      <IntroMessages text={world?.introduction} />
    </Chat>
  )
}

/** The chat after a world's last level: the world's conclusion */
export function WorldConclusionChat() {
  const worldConclusion = useAtomValue(worldConclusionAtom)
  return (
    <Chat buttons={<HomeButton />}>
      <IntroMessages text={worldConclusion} variant="conclusion" />
    </Chat>
  )
}

/** Reveals the next hidden hint of the current proof step */
function NextHintButton({
  onClick,
  className,
}: {
  onClick: () => void
  className?: string
}) {
  const { t } = useTranslation()
  return (
    <Button className={className} onClick={onClick}>
      {t('chat.nextHint')}
    </Button>
  )
}

/**
 * Whether the messages of a proof step are `deleted`: while an earlier command is edited
 * in place, the steps from there on are removed once it is executed
 */
function useDeletedSteps() {
  const editingStep = useAtomValue(editingStepAtom)
  return (step: number) => editingStep !== null && step >= editingStep
}

/**
 * The hints of the proof step `step`, as messages, grey if `deleted`. In the chat they
 * select the step on focus, inline in the proof the step itself does.
 */
function HintMessages({
  hints,
  step,
  selectable = false,
  deleted = false,
}: {
  hints: ApiHint[]
  step: number
  selectable?: boolean
  deleted?: boolean
}) {
  const gameT = useChatTranslation()
  const variant = (hint: ApiHint) =>
    deleted ? 'deleted' : hint.hidden ? 'hidden' : 'default'
  return hints.map((hint, j) =>
    selectable ? (
      <StepMessage key={j} step={step} variant={variant(hint)}>
        {hintText(hint, gameT)}
      </StepMessage>
    ) : (
      <ChatMessage key={j} variant={variant(hint)}>
        {hintText(hint, gameT)}
      </ChatMessage>
    ),
  )
}

/**
 * The chat of a level: its introduction, followed by the hints of each proof step.
 * Hidden hints are revealed one by one with "Next hint", at the current step. Once
 * the current proof is complete without warnings, the level's conclusion is shown and
 * "Next" is enabled to go on. While a command is edited, the messages of the steps it
 * would remove are grey.
 */
export function LevelChat() {
  const { data: levelInfo } = useAtomValue(levelInfoAtom)
  const { hints, current, hiddenLeft, revealNextHint, completed, newestKey } =
    useLevelHints()
  const isDeleted = useDeletedSteps()
  const buttons = (
    <>
      {hiddenLeft && <NextHintButton onClick={revealNextHint} />}
      <NextButton disabled={!completed} />
    </>
  )
  return (
    <Chat buttons={buttons} newestKey={newestKey}>
      <IntroMessages text={levelInfo?.introduction} step={0} />
      {hints.map((stepHints, i) => (
        <HintMessages
          key={i}
          hints={stepHints}
          step={i}
          selectable
          deleted={isDeleted(i)}
        />
      ))}
      {completed && (
        <IntroMessages
          text={levelInfo?.conclusion}
          step={current}
          variant={isDeleted(current) ? 'deleted' : 'conclusion'}
        />
      )}
    </Chat>
  )
}

/**
 * On mobile, where the chat is closed, its messages of the proof step `step` inside the
 * proof: the level's introduction for the initial step, the hints, and at the current
 * step "Next hint"
 */
export function InlineHints({ step }: { step: number }) {
  const { data: levelInfo } = useAtomValue(levelInfoAtom)
  const { hints, current, hiddenLeft, revealNextHint } = useLevelHints()
  const isDeleted = useDeletedSteps()
  return (
    <>
      {step === 0 && <IntroMessages text={levelInfo?.introduction} />}
      <HintMessages
        hints={hints[step] ?? []}
        step={step}
        deleted={isDeleted(step)}
      />
      {step === current && hiddenLeft && (
        <NextHintButton className="mb-2.5" onClick={revealNextHint} />
      )}
    </>
  )
}

/** On mobile, where the chat is closed, the level's conclusion below the proof */
export function InlineConclusion() {
  const { data: levelInfo } = useAtomValue(levelInfoAtom)
  const { current, completed } = useLevelHints()
  const isDeleted = useDeletedSteps()
  if (!completed) return null
  return (
    <IntroMessages
      text={levelInfo?.conclusion}
      variant={isDeleted(current) ? 'deleted' : 'conclusion'}
    />
  )
}

/**
 * On mobile, "Next" below the proof once one can go on. It takes the place of the input
 * line, which is hidden then.
 */
export function InlineNextButton() {
  const { completed } = useLevelHints()
  if (!completed) return null
  return (
    <ButtonRow>
      <NextButton disabled={false} />
    </ButtonRow>
  )
}
