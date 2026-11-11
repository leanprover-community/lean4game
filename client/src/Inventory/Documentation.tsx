import { faLock, faXmark } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtomValue, useSetAtom } from 'jotai'
import { Fragment } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import type { ApiInventoryTile } from '../api'
import { Link } from '../components/Link'
import { Markdown } from '../components/Markdown'
import { gameIdAtom, gamePath } from '../state/location-atoms'
import { difficultyAtom } from '../state/progress-atoms'
import { gameInfoAtom } from '../state/query-atoms'
import { useGameTranslation } from '../utils/translation'
import {
  closeDocAtom,
  docAtomFamily,
  inventoryAtom,
  inventoryTabAtom,
} from './inventory-atoms'

const iconButtonClass = twMerge(
  'flex size-8 shrink-0 cursor-pointer items-center justify-center rounded',
  'hover:bg-primary/15',
)

/** The lock before the name of a locked item, like a superscript */
const lockClass = 'mr-1 align-super text-xs text-gray-400'

/** The documentation of an inventory item, covering the inventory */
export function Documentation({ tile }: { tile: ApiInventoryTile }) {
  const { t } = useTranslation()
  const gameId = useAtomValue(gameIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const { t: gameT } = useGameTranslation(
    gameId ?? '',
    gameInfo?.settings?.allowEmptyTranslations,
  )
  const tab = useAtomValue(inventoryTabAtom)
  const { data: doc } = useAtomValue(docAtomFamily([tab, tile.name]))
  const difficulty = useAtomValue(difficultyAtom)
  const addToInventory = useSetAtom(inventoryAtom)
  const closeDoc = useSetAtom(closeDocAtom)
  // on the easiest difficulty, everything can be used
  const locked = difficulty > 0 && tile.locked
  const worldTitle = (world: string) =>
    gameT(gameInfo?.worlds?.nodes[world]?.title ?? world)
  /** a link to the level, closing the documentation */
  const levelLink = (world: string, level: number) =>
    gameId && (
      <Link href={gamePath(gameId, world, level)} onClick={closeDoc}>
        {t('inventory.worldLevel', { world: worldTitle(world), level })}
      </Link>
    )
  const world = tile.world ?? undefined
  const proven = tile.proven && world !== undefined && tile.level !== null
  const introducedIn = doc?.introducedIn ?? []
  const mathlibDoc = doc?.mathlibDoc

  return (
    <div className="absolute inset-0 z-10 overflow-y-auto bg-(--bg) p-4">
      <button
        type="button"
        className={twMerge(iconButtonClass, 'float-right text-xl')}
        title={t('inventory.close')}
        aria-label={t('inventory.close')}
        onClick={closeDoc}
      >
        <FontAwesomeIcon icon={faXmark} />
      </button>
      <h1 className="mt-2 mb-1 text-2xl font-black text-(--text-h)">
        {/* with the medium rules, locked items can be unlocked by hand */}
        {locked &&
          (difficulty === 1 ? (
            <button
              type="button"
              className={twMerge(
                lockClass,
                'cursor-pointer hover:text-primary',
              )}
              title={t('inventory.unlock')}
              aria-label={t('inventory.unlock')}
              onClick={() => {
                addToInventory([tile.name])
                closeDoc()
              }}
            >
              <FontAwesomeIcon icon={faLock} />
            </button>
          ) : (
            <span className={lockClass} title={t('inventory.notUnlocked')}>
              <FontAwesomeIcon icon={faLock} />
              <span className="sr-only">{t('inventory.notUnlocked')}</span>
            </span>
          ))}
        {tile.displayName}
      </h1>
      {doc?.statement && (
        <p className="mb-2">
          <code className="text-sm">{doc.statement}</code>
        </p>
      )}
      <Markdown game={gameId?.replace(/^g\//, '')}>
        {gameT(doc?.content ?? '')}
      </Markdown>
      {(proven || introducedIn.length > 0 || mathlibDoc) && (
        <>
          <h2 className="mt-4 mb-1 text-xl font-bold text-(--text-h)">
            {t('inventory.furtherDetails')}
          </h2>
          <ul className="mx-6 list-disc">
            {introducedIn.length > 0 && (
              <li>
                {t('inventory.introducedIn')}{' '}
                {introducedIn.map((it, i) => (
                  <Fragment key={`${it.world}-${it.level}`}>
                    {i > 0 && ', '}
                    {levelLink(it.world, it.level)}
                  </Fragment>
                ))}
              </li>
            )}
            {proven && (
              <li>
                {t('inventory.provenIn')} {levelLink(world, tile.level!)}
              </li>
            )}
            {mathlibDoc && (
              <li>
                <a href={mathlibDoc} target="_blank" rel="noopener noreferrer">
                  {t('inventory.mathlibDoc')}
                </a>
              </li>
            )}
          </ul>
        </>
      )}
    </div>
  )
}
