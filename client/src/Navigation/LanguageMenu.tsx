import { faXmark } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useTranslation } from 'react-i18next'

import { LanguageIcon } from '../components/LanguageIcon'
import config from '../config.json'
import { setLanguage } from '../i18n'
import { NavButton } from './NavButton'

/** The current language, opening the language menu */
export function LanguageButton({
  open,
  onToggle,
}: {
  open: boolean
  onToggle: () => void
}) {
  const { t, i18n } = useTranslation()
  return (
    <NavButton
      iconElement={
        // fixed height: the language code is lower than the icon and the flags
        <span className="inline-flex h-4 w-6 items-center justify-center">
          {open ? (
            <FontAwesomeIcon icon={faXmark} />
          ) : (
            <LanguageIcon iso={i18n.language} />
          )}
        </span>
      }
      title={
        open ? t('appBar.closeLanguageMenu') : t('appBar.openLanguageMenu')
      }
      onClick={onToggle}
    />
  )
}

/** All languages to choose from */
export function LanguageMenu() {
  return config.languages.map(({ iso, name }) => (
    <NavButton
      key={iso}
      iconElement={<LanguageIcon iso={iso} />}
      text={name}
      title={name}
      onClick={() => setLanguage(iso)}
    />
  ))
}
