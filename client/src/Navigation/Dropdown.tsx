import type { ReactNode } from 'react'
import { twMerge } from 'tailwind-merge'

/** A dropdown below the app bar, aligned to the right unless `className` says otherwise */
export function Dropdown({
  open,
  onClose,
  className,
  children,
}: {
  open: boolean
  onClose: () => void
  className?: string
  children: ReactNode
}) {
  if (!open) return null
  return (
    // clicks on the (focusable) items bubble up here, also when triggered by keyboard
    // oxlint-disable-next-line jsx-a11y/click-events-have-key-events, jsx-a11y/no-static-element-interactions
    <div
      className={twMerge(
        'absolute top-full right-0 z-10 flex-col max-h-[calc(100dvh-100%)]',
        'overflow-y-auto overscroll-contain rounded-bl-lg bg-primary py-1',
        'shadow-lg *:justify-start *:rounded-none',
        className,
      )}
      onClick={onClose}
    >
      {children}
    </div>
  )
}
