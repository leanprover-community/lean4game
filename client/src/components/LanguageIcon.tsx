import { useAtomValue } from 'jotai'
import { ReactCountryFlag } from 'react-country-flag'
import { twMerge } from 'tailwind-merge'

import config from '../config.json'
import { preferencesAtom } from '../state/preferences-atoms'

export function LanguageIcon({
  iso,
  title,
  className,
}: {
  iso: string
  title?: string
  className?: string
}) {
  const { useFlags } = useAtomValue(preferencesAtom)
  const language = config.languages.find(l => l.iso === iso)
  const flag = language?.flag
  title ??= language?.name ?? iso
  if (useFlags && flag)
    return (
      <span
        className={twMerge(
          'inline-flex h-4 w-6 items-center justify-center',
          // a drop shadow follows the flag's outline, so white flags stand out on white
          '[&_img]:drop-shadow-[1px_1px_1px_rgb(0_0_0/0.35)]',
          className,
        )}
        title={title}
      >
        <ReactCountryFlag countryCode={flag} svg />
      </span>
    )
  return (
    <span
      className={twMerge(
        // longer codes like `pt-br` grow
        'inline-block min-w-6 text-center leading-none lowercase text-sm',
        className,
      )}
      title={title}
    >
      {iso}
    </span>
  )
}
