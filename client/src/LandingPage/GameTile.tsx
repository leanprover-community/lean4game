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
 * there `1rem` was `16px`. The whole tile links to the game.
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

  return (
    <article
      className={twMerge(
        'relative flex-col w-full max-w-125 cursor-pointer justify-between',
        'justify-self-center rounded-2xl border border-neutral-400 text-left',
        'text-base leading-normal tracking-normal text-(--text-h) shadow-tile',
        // links in the text are above the link covering the whole tile
        '[&_a]:no-underline [&_a:not(.tile-link)]:relative',
        '[&_a:not(.tile-link)]:z-10',
      )}
    >
      <div>
        <div className="mx-2.5 pt-3.75 pb-1.25 text-2xl/normal font-bold">
          {/* covers the whole tile, links in the text are placed above it */}
          <Link
            className="tile-link text-inherit after:absolute after:inset-0"
            href={gamePath(`g/${game}`)}
          >
            {gameT(tile.title)}
          </Link>
        </div>
        <div className="mx-2.5 h-26 py-1.25">{gameT(tile.short)}</div>
        <div
          className={twMerge(
            'h-50 w-full',
            // behind the image, or instead of it
            'bg-linear-137 from-purple-900 to-cyan-400',
          )}
        >
          <img
            className="h-full w-full object-cover"
            src={`/api/data/${game}/${tile.image}`}
            alt=""
          />
        </div>

        <div className="mx-2.5">
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
                {gameT(tile.prerequisites.join(', '))}
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
