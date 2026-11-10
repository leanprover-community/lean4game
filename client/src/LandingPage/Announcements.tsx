import { useAtomValue } from 'jotai'
import { useTranslation } from 'react-i18next'
import Markdown from 'react-markdown'
import { twMerge } from 'tailwind-merge'

import { configAtom, localize } from '../state/config'
import { Section } from './Section'

/** The announcements from the server config, if any */
export function Announcements() {
  const { i18n } = useTranslation()
  const announcements = useAtomValue(configAtom).data?.announcements
  if (!announcements?.length) return null
  return (
    <Section>
      {announcements.map(({ title, message }, i) => (
        <article
          key={i}
          className={twMerge(
            'wrap-anywhere [&_a]:no-underline [&_p+p]:mt-3',
            // a line between the announcements
            i > 0 && 'mt-6 border-t border-neutral-300 pt-6',
            i > 0 && 'dark:border-neutral-600',
          )}
        >
          <h2>{localize(title, i18n.language)}</h2>
          <Markdown>{localize(message, i18n.language)}</Markdown>
        </article>
      ))}
    </Section>
  )
}
