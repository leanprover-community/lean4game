import { useAtomValue } from 'jotai'
import type { ReactNode } from 'react'
import { Trans, useTranslation } from 'react-i18next'

import { Markdown } from '../components/Markdown'
import { Popup } from '../components/Popup'
import { IssueLink } from '../ErrorPage/ErrorMessage'
import { gameIdAtom } from '../state/location-atoms'
import { gameInfoAtom } from '../state/query-atoms'
import { useGameTranslation } from '../utils/translation'

const REPO = 'https://github.com/leanprover-community/lean4game'

/** A link opening in a new tab, its text is passed by `<Trans>` */
function ExternalLink({
  href,
  children,
}: {
  href: string
  children?: ReactNode
}) {
  return (
    <a href={href} target="_blank" rel="noreferrer">
      {children}
    </a>
  )
}

/** The sections about the server below the game's info */
const SECTIONS = [
  'progressSaving',
  'accessibility',
  'development',
  'funding',
] as const

/** The info about the current game from its `game.json`, and about the server */
export function GameInfoPopup({
  open,
  onClose,
}: {
  open: boolean
  onClose: () => void
}) {
  const { t } = useTranslation()
  const gameId = useAtomValue(gameIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const { t: gameT } = useGameTranslation(
    gameId ?? '',
    gameInfo?.settings?.allowEmptyTranslations,
  )

  return (
    <Popup open={open} onClose={onClose} title={t('appBar.gameInfoTitle')}>
      <div className="[&_h2]:mt-4 [&_h2]:mb-1 [&_h2]:text-lg [&_h2]:font-bold [&_p]:my-2">
        {gameInfo?.info && (
          <Markdown game={gameId?.replace(/^g\//, '')}>
            {gameT(gameInfo.info)}
          </Markdown>
        )}
        <hr className="my-4 border-(--border)" />
        {SECTIONS.map(section => (
          <section key={section}>
            <h2>{t(`gameInfo.${section}.title`)}</h2>
            <p>
              <Trans
                i18nKey={`gameInfo.${section}.description`}
                components={{
                  br: <br />,
                  strong: <strong />,
                  i: <i />,
                  githubLink: <ExternalLink href={REPO} />,
                  issueLink: <IssueLink />,
                  adamLink: <ExternalLink href="https://hhu-adam.github.io" />,
                }}
              />
            </p>
          </section>
        ))}
      </div>
    </Popup>
  )
}
