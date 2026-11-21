import { type MouseEvent, useRef } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import type { ApiGameInfo } from '../api'
import { LanguageIcon } from '../components/LanguageIcon'
import { Link } from '../components/Link'
import { Markdown } from '../components/Markdown'
import config from '../config.json'
import { gamePath } from '../state/location-atoms'
import { useGameTranslation } from '../utils/translation'

/** Sort languages for uniformity */
function sortLanguages(languages: string[]) {
  const order = config.languages.map(language => language.iso)
  const rank = (iso: string) => {
    const i = order.indexOf(iso)
    return i === -1 ? order.length : i
  }
  return languages.toSorted((a, b) => rank(a) - rank(b) || a.localeCompare(b))
}

/**
 * A game on the landing page. The styling is the one of the old client, in pixels as
 * there `1rem` was `16px`. The whole tile links to the game: clicks anywhere on it are
 * forwarded to the link in the title, except clicks on other links and clicks that end
 * a text selection.
 */
export function GameTile({
  owner,
  repo,
  tile,
  settings,
}: ApiGameInfo & { tile: NonNullable<ApiGameInfo['tile']> }) {
  const { t } = useTranslation()
  const game = `${owner}/${repo}`
  const { t: gameT } = useGameTranslation(
    `g/${game}`,
    settings?.allowEmptyTranslations,
  )
  const titleLink = useRef<HTMLAnchorElement>(null)
  const href = gamePath(`g/${game}`)

  function handleClick(event: MouseEvent<HTMLElement>) {
    const target = event.target as HTMLElement
    if (target.closest('a') || window.getSelection()?.toString()) return
    if (event.ctrlKey || event.metaKey || event.shiftKey) {
      window.open(href, '_blank', 'noopener')
    } else {
      titleLink.current?.click()
    }
  }

  return (
    // The title receives focus and has the same action as the onClick here
    // oxlint-disable-next-line jsx-a11y/click-events-have-key-events, jsx-a11y/no-noninteractive-element-interactions
    <article
      onClick={handleClick}
      className={twMerge(
        'flex-col w-full max-w-125 cursor-pointer justify-between',
        'justify-self-center rounded-2xl border border-neutral-400 text-left',
        'text-base leading-normal tracking-normal text-(--text-h) shadow-tile',
        '[&_a]:no-underline',
      )}
    >
      <div>
        <div className="mx-2.5 pt-3.75 pb-1.25 text-2xl/normal font-bold">
          <Link ref={titleLink} className="text-inherit" href={href}>
            {gameT(tile.title)}
          </Link>
        </div>
        <div className="mx-2.5 box-content line-clamp-2 h-[2lh] pt-1.25 pb-4">
          {gameT(tile.short)}
        </div>
        <div
          className={'h-50 w-full bg-linear-137 from-purple-900 to-cyan-400'}
        >
          <img
            className="h-full w-full object-cover"
            src={`/api/data/${game}/${tile.image}`}
            alt=""
          />
        </div>

        <div
          className={twMerge(
            'mx-2.5 py-4 [&_p]:my-4',
            '[&>div>:first-child]:mt-0 [&>div>:last-child]:mb-0',
          )}
        >
          <Markdown game={game}>{gameT(tile.long)}</Markdown>
        </div>
      </div>
      <table
        className={twMerge(
          'mx-2.5 mt-1.25 mb-3.75 border-collapse',
          '[&_td]:py-1.25 [&_td:nth-child(even)]:text-right',
          '[&_tr]:border-y [&_tr]:border-neutral-300',
          'dark:[&_tr]:border-neutral-600',
        )}
      >
        <tbody>
          <tr>
            <td title={t('landing.tile.prerequisitesTitle')}>
              {t('landing.tile.prerequisites')}
            </td>
            <td>
              <Markdown game={game}>
                {gameT(
                  typeof tile.prerequisites === 'string'
                    ? tile.prerequisites
                    : tile.prerequisites.join(', '),
                )}
              </Markdown>
            </td>
          </tr>
          <tr>
            <td>{t('landing.tile.worlds')}</td>
            <td>{tile.worlds}</td>
          </tr>
          <tr>
            <td>{t('landing.tile.levels')}</td>
            <td>{tile.levels}</td>
          </tr>
          <tr>
            <td>{t('landing.tile.languages')}</td>
            <td>
              {sortLanguages(tile.languages).map((iso, i) => (
                <LanguageIcon
                  key={iso}
                  iso={iso}
                  className={twMerge(
                    'inline w-auto text-left leading-[inherit]',
                    i > 0 && 'ml-2',
                  )}
                />
              ))}
            </td>
          </tr>
        </tbody>
      </table>
    </article>
  )
}
