import { useAtomValue } from 'jotai'
import { useTranslation } from 'react-i18next'

import { ContactInfo, LegalPage } from '../components/LegalPage'
import { configAtom, localise } from '../state/config'

export function PrivacyPage() {
  return <LegalPage Content={PrivacyPolicy} />
}

function PrivacyPolicy({ lng }: { lng: string }) {
  const { t } = useTranslation(undefined, { lng })
  const serverLocation = useAtomValue(configAtom).data?.privacy?.serverLocation
  return (
    <div className="max-w-3xl">
      <h2>{t('privacy.title')}</h2>
      <p>{t('privacy.collectedData')}</p>
      <p>{t('privacy.browserStorage')}</p>
      {serverLocation && (
        <p>
          {t('privacy.serverLocation', {
            location: localise(serverLocation, lng),
          })}
        </p>
      )}
      <ContactInfo lng={lng} />
    </div>
  )
}
