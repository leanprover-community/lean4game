import { faWandMagicSparkles } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import {
  type ReactNode,
  type RefObject,
  type SyntheticEvent,
  useLayoutEffect,
} from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

/**
 * The typewriter's input for Lean commands: a blue frame, grey while `disabled`, with an
 * execute button. Used for the input line at the bottom and for editing earlier steps.
 * Enter or the button submits it, Ctrl+Enter (or Shift+Enter) starts a new line, Escape
 * calls `onCancel`. It grows with its content. `children` are further buttons after the
 * execute button, `className` places it.
 */
export function CommandInput({
  ref,
  value,
  onChange,
  onSubmit,
  onCancel,
  disabled,
  placeholder,
  className,
  children,
}: {
  ref: RefObject<HTMLTextAreaElement | null>
  value: string
  onChange: (value: string) => void
  onSubmit: () => void
  onCancel?: () => void
  disabled: boolean
  placeholder?: string
  className?: string
  children?: ReactNode
}) {
  const { t } = useTranslation()

  // grow with the content, up to a third of the window
  useLayoutEffect(() => {
    const textarea = ref.current
    if (!textarea) return
    textarea.style.height = 'auto'
    textarea.style.height = `${Math.min(textarea.scrollHeight, window.innerHeight / 3)}px`
  }, [ref, value])

  const submit = (ev: SyntheticEvent) => {
    ev.preventDefault()
    if (!disabled && value.trim().length > 0) onSubmit()
  }

  return (
    <form
      className={twMerge(
        'flex items-end gap-2 bg-primary p-2',
        disabled && 'bg-gray-300 dark:bg-gray-700',
        className,
      )}
      onSubmit={submit}
    >
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
        onChange={ev => onChange(ev.target.value)}
        onKeyDown={ev => {
          if (ev.key === 'Escape' && onCancel) {
            ev.preventDefault()
            onCancel()
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
            onChange(textarea.value)
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
