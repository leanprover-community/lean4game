import { faArrowRight, faHome } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtomValue, useSetAtom } from 'jotai'
import { type HTMLAttributes, type ReactNode, useEffect, useRef } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import type { ApiHint } from '../api'
import { Button, LinkButton } from '../components/Button'
import { Markdown } from '../components/Markdown'
import {
  useScrollToSelectedStep,
  useStepSelection,
} from '../hooks/useStepSelection'
import { readGameIntroAtom } from '../state/chat-atoms'
import { leftPanelOpenAtom } from '../state/layout-atoms'
import {
  gameIdAtom,
  gamePath,
  levelIdAtom,
  worldIdAtom,
} from '../state/location-atoms'
import { mobileAtom } from '../state/preferences-atoms'
import { readWorldIntroAtom } from '../state/progress-atoms'
import { gameInfoAtom, levelInfoAtom } from '../state/query-atoms'
import { useGameTranslation } from '../utils/translation'
import { useLevelHints } from './useLevelHints'

type GameT = (key: string | undefined) => string

/** The translation of the current game's texts */
function useChatTranslation() {
  const gameId = useAtomValue(gameIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const { t: gameT } = useGameTranslation(
    gameId ?? '',
    gameInfo?.settings?.allowEmptyTranslations,
  )
  return gameT
}

/** Splits an introduction into messages at blank lines */
function splitIntro(text: string) {
  return text.split(/\n(\s*\n)+/).filter(part => part.trim())
}

/**
 * The translated text of a hint, with the variable names marked like `«{g}»` replaced
 * by the ones the player used
 */
function hintText(hint: ApiHint, gameT: GameT) {
  // hints created in the frontend do not have a `rawText`
  if (!hint.rawText) return gameT(hint.text)
  return gameT(hint.rawText).replaceAll(
    /«\{(.*?)\}»/g,
    (_, v: string) => hint.varNames.find(x => x[0] === v)?.[1] ?? '',
  )
}

type ChatMessageProps = {
  children: string
  hidden?: boolean
} & Omit<HTMLAttributes<HTMLDivElement>, 'children'>

/** A message of the chat, yellow for hidden hints */
function ChatMessage({
  children,
  hidden = false,
  className,
  ...props
}: ChatMessageProps) {
  const gameId = useAtomValue(gameIdAtom)
  return (
    <div
      className={twMerge(
        'my-2.5 overflow-x-auto rounded-sm px-2.5 py-1.5',
        hidden
          ? 'bg-amber-100 text-amber-800 dark:bg-amber-950 dark:text-amber-200'
          : 'bg-sky-100 text-(--text-h) dark:bg-sky-950',
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
  if (gameInfo?.worldSize?.[worldId] === 0) {
    return (
      <ForwardButton href={gamePath(gameId)}>
        <FontAwesomeIcon icon={faHome} />
        &nbsp;{t('appBar.home')}
      </ForwardButton>
    )
  }
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

/** Goes to the next level, or home after the world's last level */
function NextButton({ disabled }: { disabled: boolean }) {
  const { t } = useTranslation()
  const gameId = useAtomValue(gameIdAtom)
  const worldId = useAtomValue(worldIdAtom)
  const levelId = useAtomValue(levelIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const worldSize =
    worldId === undefined ? undefined : gameInfo?.worldSize?.[worldId]
  if (
    gameId === undefined ||
    worldId === undefined ||
    levelId === undefined ||
    worldSize === undefined
  )
    return null
  if (levelId >= worldSize) {
    return (
      <ForwardButton href={gamePath(gameId)} disabled={disabled}>
        <FontAwesomeIcon icon={faHome} />
        &nbsp;{t('appBar.home')}
      </ForwardButton>
    )
  }
  return (
    <ForwardButton
      href={gamePath(gameId, worldId, levelId + 1)}
      disabled={disabled}
    >
      {t('appBar.next')}&nbsp;
      <FontAwesomeIcon icon={faArrowRight} />
    </ForwardButton>
  )
}

/**
 * An introduction, one message per paragraph. On a level, it belongs to the initial
 * proof step `step`.
 */
function IntroMessages({
  text,
  step,
}: {
  text: string | null | undefined
  step?: number
}) {
  const gameT = useChatTranslation()
  return splitIntro(gameT(text ?? '')).map((part, i) =>
    step === undefined ? (
      <ChatMessage key={i}>{part}</ChatMessage>
    ) : (
      <StepMessage key={i} step={step}>
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

/** The chat on the game overview: the game's introduction */
export function GameChat() {
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const mobile = useAtomValue(mobileAtom)
  return (
    <Chat buttons={mobile && <GameStartButton />}>
      <IntroMessages text={gameInfo?.introduction} />
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
 * The hints of the proof step `step`, as messages. In the chat they select the step on
 * focus, inline in the proof the step itself does.
 */
function HintMessages({
  hints,
  step,
  selectable = false,
}: {
  hints: ApiHint[]
  step: number
  selectable?: boolean
}) {
  const gameT = useChatTranslation()
  return hints.map((hint, j) =>
    selectable ? (
      <StepMessage key={j} step={step} hidden={hint.hidden}>
        {hintText(hint, gameT)}
      </StepMessage>
    ) : (
      <ChatMessage key={j} hidden={hint.hidden}>
        {hintText(hint, gameT)}
      </ChatMessage>
    ),
  )
}

/**
 * The chat of a level: its introduction, followed by the hints of each proof step.
 * Hidden hints are revealed one by one with "Next hint", at the current step. Once
 * the current proof is complete without warnings, "Next" is enabled to go on.
 */
export function LevelChat() {
  const { data: levelInfo } = useAtomValue(levelInfoAtom)
  const { hints, hiddenLeft, revealNextHint, completed, newestKey } =
    useLevelHints()
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
        <HintMessages key={i} hints={stepHints} step={i} selectable />
      ))}
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
  return (
    <>
      {step === 0 && <IntroMessages text={levelInfo?.introduction} />}
      <HintMessages hints={hints[step] ?? []} step={step} />
      {step === current && hiddenLeft && (
        <NextHintButton className="mb-2.5" onClick={revealNextHint} />
      )}
    </>
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
