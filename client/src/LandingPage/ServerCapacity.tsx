import { useAtomValue } from 'jotai'
import { Trans, useTranslation } from 'react-i18next'

import { activePlayersAtom, serverLoadAtom } from './landing-atoms'
import { Section } from './Section'

const percent = (value: number) => (100 * value).toFixed(0)

/** The current load of the server, hidden if unavailable */
export function ServerCapacity() {
  const { t } = useTranslation()
  const { data: load } = useAtomValue(serverLoadAtom)
  const { data: players } = useAtomValue(activePlayersAtom)
  if (!load) return null
  return (
    <Section title={t('landing.capacity.title')}>
      <p>{t('landing.capacity.description')}</p>
      <p>
        {players !== undefined && (
          <>
            <Trans
              i18nKey="landing.capacity.players"
              values={{ count: players }}
            />
            <br />
          </>
        )}
        <Trans
          i18nKey="landing.capacity.memory"
          values={{ value: percent(load.memory) }}
        />
        <br />
        <Trans
          i18nKey="landing.capacity.cpu"
          values={{ value: percent(load.cpu) }}
        />
      </p>
    </Section>
  )
}
