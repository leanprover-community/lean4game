import { useAtomValue } from 'jotai'
import { type ComponentType, Fragment } from 'react'
import { useTranslation } from 'react-i18next'

import { configAtom, localise } from '../state/config'

/**
 * Layout of the impressum and the privacy policy. If the current language is translated,
 * the translated version is followed by the English original.
 */
export function LegalPage({
  Content,
}: {
  Content: ComponentType<{ lng: string }>
}) {
  const { t, i18n } = useTranslation()
  const lng = i18n.resolvedLanguage ?? 'en'
  // without a translation, the "translated" version would also be English
  const isTranslated =
    lng !== 'en' &&
    i18n.getResource(lng, 'translation', 'legal.englishBelow') !== undefined
  return (
    <div className="mx-auto flex-col w-full max-w-3xl gap-4 p-8 text-left">
      {isTranslated && (
        <>
          <p className="italic">{t('legal.englishBelow')}</p>
          <Content lng={lng} />
          <hr className="my-4 w-full border-(--border)" />
        </>
      )}
      <Content lng="en" />
    </div>
  )
}

/** The contact information from the server config, in the language `lng` */
export function ContactInfo({ lng }: { lng: string }) {
  const { t } = useTranslation(undefined, { lng })
  const { data: legal, isError } = useAtomValue(configAtom)
  if (isError) return <p>{t('legal.loadError')}</p>
  const contact = legal?.contact
  if (!contact) return null
  return (
    <p>
      <strong>{t('legal.contact')}</strong>
      <br />
      {contact.name}
      <br />
      {contact.address.map((line, i) => (
        <Fragment key={i}>
          {localise(line, lng)}
          <br />
        </Fragment>
      ))}
      {contact.phone && (
        <>
          {contact.phone}
          <br />
        </>
      )}
      {contact.url && (
        <>
          <a href={contact.url} target="_blank" rel="noreferrer">
            {t('legal.contactDetails')}
          </a>
          <br />
        </>
      )}
      {contact.technicalEmail && (
        <a href={`mailto:${contact.technicalEmail}?subject=leangame`}>
          {t('legal.technicalContact')}
        </a>
      )}
    </p>
  )
}
