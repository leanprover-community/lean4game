import { useAtom } from 'jotai'
import { useEffect } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { rawCopyAtom } from './raw-insert-atoms'

/** How long the toast about a copy is shown */
const TOAST_MS = 2500

/**
 * Says that clicking an insertion button copied its text to the clipboard, see
 * `insertInRawAtom`. At the top of the mask, not scrolling with it.
 */
export function CopyToast() {
  const { t } = useTranslation()
  const [copy, setCopy] = useAtom(rawCopyAtom)

  // hide it after a while, unless there was another copy in the meantime
  useEffect(() => {
    const timeout = setTimeout(() => {
      if (copy) setCopy(current => (current?.id === copy.id ? null : current))
    }, TOAST_MS)
    return () => clearTimeout(timeout)
  }, [copy, setCopy])

  return (
    // always there, so that screen readers announce the changes
    <output className="pointer-events-none absolute inset-x-2 top-2 flex justify-center">
      {copy && (
        <span
          className={twMerge(
            'rounded-sm px-3 py-1.5 font-sans text-sm shadow-md',
            copy.copied
              ? 'bg-gray-800 text-white dark:bg-gray-200 dark:text-gray-900'
              : 'bg-red-100 text-red-700 dark:bg-red-950 dark:text-red-300',
          )}
        >
          {t(copy.copied ? 'masks.copied' : 'masks.copyFailed', {
            text: copy.text,
          })}
        </span>
      )}
    </output>
  )
}
