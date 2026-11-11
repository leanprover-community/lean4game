import { atom, type PrimitiveAtom, useAtom } from 'jotai'
import { useEffect } from 'react'
import { twMerge } from 'tailwind-merge'

/** How long a toast is shown */
const TOAST_MS = 2500

/** A short message, e.g. that clicking a button copied something */
export interface ToastMessage {
  text: string
  /** shown in red */
  error?: boolean
}

/** A message of a `Toast`, `null` while there is none */
export type ToastAtom = PrimitiveAtom<ToastMessage | null>

/** The message of a `Toast`. Setting it shows the toast, also for the same text again. */
export function toastAtom(): ToastAtom {
  return atom<ToastMessage | null>(null)
}

/**
 * Shows the message of `messageAtom` for a while, at the top of its positioned parent,
 * not scrolling with it. A new message replaces the old one and starts over.
 */
export function Toast({ messageAtom }: { messageAtom: ToastAtom }) {
  const [message, setMessage] = useAtom(messageAtom)

  // a new message object restarts the timer, even with the same text
  useEffect(() => {
    const timeout = setTimeout(() => {
      if (message) setMessage(null)
    }, TOAST_MS)
    return () => clearTimeout(timeout)
  }, [message, setMessage])

  return (
    // always there, so that screen readers announce the changes
    <output className="pointer-events-none absolute inset-x-2 top-2 z-10 flex justify-center">
      {message && (
        <span
          className={twMerge(
            'rounded-sm px-3 py-1.5 font-sans text-sm shadow-md',
            message.error
              ? 'bg-red-100 text-red-700 dark:bg-red-950 dark:text-red-300'
              : 'bg-gray-800 text-white dark:bg-gray-200 dark:text-gray-900',
          )}
        >
          {message.text}
        </span>
      )}
    </output>
  )
}
