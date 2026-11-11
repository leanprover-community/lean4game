import { faWandMagicSparkles } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import {
  type ReactNode,
  type RefObject,
  type SyntheticEvent,
  useLayoutEffect,
  useSyncExternalStore,
} from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { abbreviationSuggestions, useAbbreviations } from './useAbbreviations'

/**
 * While an abbreviation is typed, a bar on top of the input with the first symbols it
 * could become. The first one is what space or Tab would insert.
 */
function AbbreviationBar({
  abbreviations,
}: {
  abbreviations: ReturnType<typeof useAbbreviations>
}) {
  const typed = useSyncExternalStore(
    abbreviations.subscribe,
    abbreviations.typed,
  )
  // a lone backslash would match everything, with no sensible order
  if (!typed) return null
  const suggestions = abbreviationSuggestions(typed, 5)
  if (suggestions.length === 0) return null
  return (
    <div
      className={twMerge(
        'absolute inset-x-0 bottom-full z-10 flex h-8 items-center gap-1 px-1',
        'border-t border-primary bg-sky-100 text-(--text-h) dark:bg-sky-950 rounded-t-lg',
      )}
    >
      {suggestions.map(({ symbol, abbreviation }, i) => (
        <button
          key={abbreviation}
          type="button"
          className={twMerge(
            'flex h-6 min-w-0 flex-1 basis-0 cursor-pointer items-baseline',
            'justify-center gap-1.5 overflow-hidden rounded-sm px-1.5',
            'hover:bg-primary/25',
            i === 0 && 'bg-primary/15',
          )}
          // keep the focus and the cursor in the input
          onMouseDown={ev => ev.preventDefault()}
          onClick={() => void abbreviations.accept(abbreviation)}
        >
          <span className="shrink-0 font-mono font-bold">
            {symbol.replace('$CURSOR', '')}
          </span>
          <span className="truncate text-xs opacity-70">{abbreviation}</span>
        </button>
      ))}
    </div>
  )
}

/**
 * The typewriter's input for Lean commands: a blue frame, grey while `disabled`, with an
 * execute button. Used for the input line at the bottom and for editing earlier steps.
 * Enter or the button submits it, Ctrl+Enter (or Shift+Enter) starts a new line, Escape
 * calls `onCancel`, Tab completes a unicode abbreviation like `\to`. It grows with its
 * content. `children` are further buttons after the execute button, `className` places it.
 */
export function CommandInput({
  ref,
  value,
  onChange,
  onSubmit,
  onCancel,
  onSelectionChange,
  onFocus,
  disabled,
  placeholder,
  className,
  children,
}: {
  ref: RefObject<HTMLTextAreaElement | null>
  value: string
  onChange: (value: string) => void
  /** called with the final text, in which all abbreviations are replaced */
  onSubmit: (value: string) => void
  onCancel?: () => void
  /** called when the selection changes, also when only the caret moves */
  onSelectionChange?: (selection: [number, number]) => void
  onFocus?: () => void
  disabled: boolean
  placeholder?: string
  className?: string
  children?: ReactNode
}) {
  const { t } = useTranslation()
  const abbreviations = useAbbreviations(ref, value, onChange)

  // grow with the content, up to a third of the window
  useLayoutEffect(() => {
    const textarea = ref.current
    if (!textarea) return
    textarea.style.height = 'auto'
    textarea.style.height = `${Math.min(textarea.scrollHeight, window.innerHeight / 3)}px`
    // oxlint-disable-next-line react/exhaustive-effect-dependencies -- `value` triggers the resize
  }, [ref, value])

  const submit = (ev: SyntheticEvent) => {
    ev.preventDefault()
    if (disabled) return
    void abbreviations.replaceAll().then(text => {
      if (text.trim().length > 0) onSubmit(text)
    })
  }

  return (
    <form
      className={twMerge(
        'relative flex items-end gap-2 bg-primary p-2',
        disabled && 'bg-gray-300 dark:bg-gray-700',
        className,
      )}
      onSubmit={submit}
    >
      <AbbreviationBar abbreviations={abbreviations} />
      <textarea
        ref={ref}
        rows={1}
        value={value}
        disabled={disabled}
        aria-label={placeholder}
        placeholder={placeholder}
        className={twMerge(
          'min-h-7.5 min-w-0 flex-1 resize-none bg-(--bg) px-2.5 py-0.5',
          'font-mono text-(--text-h) outline-none',
          'disabled:bg-gray-100 disabled:text-gray-500',
          'dark:disabled:bg-gray-800 dark:disabled:text-gray-400',
        )}
        spellCheck={false}
        autoCapitalize="off"
        autoCorrect="off"
        onChange={() => abbreviations.input()}
        onFocus={onFocus}
        onSelect={ev => {
          abbreviations.select()
          const { selectionStart, selectionEnd } = ev.currentTarget
          onSelectionChange?.([selectionStart, selectionEnd])
        }}
        onCompositionStart={() => abbreviations.compositionStart()}
        onCompositionEnd={() => abbreviations.compositionEnd()}
        onKeyDown={ev => {
          if (ev.key === 'Escape' && onCancel) {
            ev.preventDefault()
            onCancel()
          }
          // otherwise Tab moves the focus as usual
          if (ev.key === 'Tab' && abbreviations.tracking) {
            ev.preventDefault()
            void abbreviations.replaceAll()
          }
          // not while composing a character with an input method
          if (ev.key !== 'Enter' || ev.nativeEvent.isComposing) return
          const textarea = ev.currentTarget
          if (ev.ctrlKey || ev.metaKey) {
            // a textarea ignores Ctrl+Enter, so insert the new line ourselves
            ev.preventDefault()
            textarea.setRangeText(
              '\n',
              textarea.selectionStart,
              textarea.selectionEnd,
              'end',
            )
            abbreviations.input()
          } else if (!ev.shiftKey) {
            submit(ev)
          }
        }}
      />
      <button
        type="submit"
        disabled={disabled}
        className={twMerge(
          'h-7.5 min-w-24 shrink-0 cursor-pointer rounded-sm bg-(--bg) px-3',
          'whitespace-nowrap text-primary',
          'disabled:cursor-default disabled:text-gray-500',
        )}
      >
        <FontAwesomeIcon icon={faWandMagicSparkles} />
        &nbsp;{t('typewriter.execute')}
      </button>
      {children}
    </form>
  )
}

/** Focuses `textarea` with the cursor at the end */
export function focusAtEnd(textarea: HTMLTextAreaElement | null) {
  if (!textarea) return
  textarea.focus()
  textarea.setSelectionRange(textarea.value.length, textarea.value.length)
}
