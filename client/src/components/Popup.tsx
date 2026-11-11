import { faXmark } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { type ReactNode, useEffect, useId, useRef } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

/**
 * A modal popup with a `title` and a close button. Closes with Escape and by clicking
 * outside of it.
 */
export function Popup({
  open,
  onClose,
  title,
  children,
}: {
  open: boolean
  onClose: () => void
  title: string
  children: ReactNode
}) {
  const { t } = useTranslation()
  const dialogRef = useRef<HTMLDialogElement>(null)
  const titleId = useId()

  useEffect(() => {
    const dialog = dialogRef.current
    if (!dialog) return
    if (open && !dialog.open) dialog.showModal()
    if (!open && dialog.open) dialog.close()
  }, [open])

  return (
    // the click closes it on the backdrop, the keyboard equivalent is Escape
    // oxlint-disable-next-line jsx-a11y/click-events-have-key-events, jsx-a11y/no-noninteractive-element-interactions
    <dialog
      ref={dialogRef}
      aria-labelledby={titleId}
      // Escape: closed through `open`, so that the state is never behind the dialog
      onCancel={e => {
        e.preventDefault()
        onClose()
      }}
      // a click on the backdrop is a click on the dialog itself
      onClick={e => {
        if (e.target === e.currentTarget) onClose()
      }}
      className={twMerge(
        // at most 36rem, with a margin of 1rem on small screens
        'm-auto max-h-[calc(100dvh-2rem)] w-[min(36rem,calc(100vw-2rem))] max-w-none',
        'rounded-lg bg-(--bg) p-0 text-left text-(--text) shadow-xl',
        'backdrop:bg-black/50',
      )}
    >
      <div className="relative px-6 pt-4 pb-6">
        <h2 id={titleId} className="mt-0 mb-3 pr-8 text-xl font-bold">
          {title}
        </h2>
        <button
          type="button"
          className={twMerge(
            'absolute top-3 right-3 flex size-8 cursor-pointer items-center',
            'justify-center rounded text-primary hover:bg-primary/15',
          )}
          title={t('popup.close')}
          aria-label={t('popup.close')}
          onClick={onClose}
        >
          <FontAwesomeIcon icon={faXmark} />
        </button>
        {children}
      </div>
    </dialog>
  )
}
