import { faBan, faLock, faReply } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtom, useAtomValue, useSetAtom } from 'jotai'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import type { ApiInventoryTile } from '../api'
import { levelIdAtom } from '../state/location-atoms'
import { difficultyAtom } from '../state/progress-atoms'
import { Documentation } from './Documentation'
import {
  currentInventoryTilesAtom,
  inventoryCurrentTabNewTilesAtom,
  inventoryCurrentTabRecentTilesAtom,
  inventorySubtabAtom,
  inventorySubtabOptionsAtom,
  InventoryTab,
  inventoryTabAtom,
  inventoryTabNewTilesAtom,
  inventoryTabRecentTilesAtom,
  selectedDocTileAtom,
} from './inventory-atoms'

const tabTitles = {
  [InventoryTab.theorem]: 'inventory.theorems',
  [InventoryTab.tactic]: 'inventory.tactics',
  [InventoryTab.definition]: 'inventory.definitions',
} as const

/**
 * The inventory with the tactics, theorems and definitions: of the current level, or of
 * the whole game outside of levels. Clicking an item opens its documentation on top.
 */
export function Inventory() {
  const doc = useAtomValue(selectedDocTileAtom)
  return (
    <div className="relative flex-col h-full text-left">
      <TabBar />
      <SubtabBar />
      <InventoryList />
      {doc && <Documentation tile={doc} />}
    </div>
  )
}

/**
 * A tab, marked yellow if it contains new items, and violet if it contains the theorem
 * of the previous level
 */
function Tab({
  active,
  hasNew,
  hasRecent,
  onClick,
  className,
  children,
}: {
  active: boolean
  hasNew: boolean
  hasRecent: boolean
  onClick: () => void
  className?: string
  children: string
}) {
  return (
    <button
      type="button"
      className={twMerge(
        'cursor-pointer border-b-4 border-transparent px-4 py-0.5 text-(--text)',
        'hover:text-(--text-h)',
        hasNew &&
          'border-amber-100 bg-linear-to-b from-transparent to-amber-100 dark:border-amber-950 dark:to-amber-950',
        hasRecent &&
          'border-fuchsia-200 bg-linear-to-b from-transparent to-fuchsia-200 dark:border-fuchsia-950 dark:to-fuchsia-950',
        active && 'border-primary text-(--text-h)',
        className,
      )}
      onClick={onClick}
    >
      {children}
    </button>
  )
}

/** Choose between theorems, tactics and definitions */
function TabBar() {
  const { t } = useTranslation()
  const [tab, setTab] = useAtom(inventoryTabAtom)
  const newTiles = useAtomValue(inventoryTabNewTilesAtom)
  const recentTiles = useAtomValue(inventoryTabRecentTilesAtom)
  return (
    <div className="flex shrink-0 flex-wrap border-b border-(--border) font-bold">
      {Object.values(InventoryTab).map(type => (
        <Tab
          key={type}
          active={tab === type}
          hasNew={newTiles[type].length > 0}
          hasRecent={recentTiles[type].length > 0}
          onClick={() => setTab(type)}
          className="flex-1 px-0 text-center"
        >
          {t(tabTitles[type])}
        </Tab>
      ))}
    </div>
  )
}

/** The categories of the current tab, if there are several */
function SubtabBar() {
  const [subtab, setSubtab] = useAtom(inventorySubtabAtom)
  const options = useAtomValue(inventorySubtabOptionsAtom)
  const newTiles = useAtomValue(inventoryCurrentTabNewTilesAtom)
  const recentTiles = useAtomValue(inventoryCurrentTabRecentTilesAtom)
  if (options.length < 2) return null
  return (
    <div className="flex shrink-0 flex-wrap border-b border-(--border)">
      {options.map(category => (
        <Tab
          key={category}
          active={category === subtab}
          hasNew={newTiles.some(it => it.category === category)}
          hasRecent={recentTiles.some(it => it.category === category)}
          onClick={() => setSubtab(category)}
        >
          {category}
        </Tab>
      ))}
    </div>
  )
}

/** The items of the current (sub)tab, in as many columns as fit the panel */
function InventoryList() {
  const tab = useAtomValue(inventoryTabAtom)
  const tiles = useAtomValue(currentInventoryTilesAtom)
  const recentTiles = useAtomValue(inventoryCurrentTabRecentTilesAtom)
  const difficulty = useAtomValue(difficultyAtom)
  const isTheorem = tab === InventoryTab.theorem
  const sorted = tiles.toSorted(
    // theorems are sorted `available > disabled > locked`, then alphabetically
    (x, y) =>
      (isTheorem && (+x.locked - +y.locked || +x.disabled - +y.disabled)) ||
      x.displayName.localeCompare(y.displayName),
  )
  return (
    <div
      className={twMerge(
        'grid min-h-0 flex-1 content-start overflow-y-auto',
        isTheorem
          ? 'grid-cols-[repeat(auto-fill,minmax(14rem,1fr))]'
          : 'grid-cols-[repeat(auto-fill,minmax(9rem,1fr))]',
      )}
    >
      {sorted.map(tile => (
        <InventoryItem
          key={`${tile.category}-${tile.name}`}
          tile={tile}
          recent={recentTiles.some(it => it.name === tile.name)}
          // on the easiest difficulty, everything can be used
          enableAll={difficulty === 0}
        />
      ))}
    </div>
  )
}

/**
 * An item: grey if locked, red if not available in this level, yellow if new in this
 * level, and violet if it is the theorem of the previous level
 */
function InventoryItem({
  tile,
  recent,
  enableAll,
}: {
  tile: ApiInventoryTile
  recent: boolean
  enableAll: boolean
}) {
  const { t } = useTranslation()
  const setDoc = useSetAtom(selectedDocTileAtom)
  const levelId = useAtomValue(levelIdAtom)
  const locked = !enableAll && tile.locked
  const insertable =
    (levelId ?? 0) > 0 && (enableAll || !(tile.locked || tile.disabled))
  // the `altTitle` of theorems has the form `Namespace.name (x y : Nat) : some type`
  const title = locked
    ? t('inventory.notUnlocked')
    : tile.disabled
      ? t('inventory.notAvailable')
      : tile.altTitle.substring(tile.altTitle.indexOf(' ') + 1)
  return (
    <div
      className={twMerge(
        'flex items-center border-b border-(--border) text-(--text-h)',
        tile.new && 'bg-amber-100 dark:bg-amber-950',
        recent && 'bg-fuchsia-200 dark:bg-fuchsia-950',
        tile.disabled && 'text-red-600 dark:text-red-400',
        locked && 'text-gray-300 dark:text-gray-600',
      )}
    >
      <button
        type="button"
        className={twMerge(
          'min-w-0 flex-1 cursor-pointer py-0.5 pl-6 text-left wrap-break-word',
          'hover:underline',
        )}
        title={title}
        onClick={() => setDoc(tile)}
      >
        {locked && <FontAwesomeIcon icon={faLock} className="mr-1" />}
        {!locked && tile.disabled && (
          <FontAwesomeIcon icon={faBan} className="mr-1" />
        )}
        {tile.displayName}
      </button>
      {insertable && (
        <button
          type="button"
          // like the names of the hypotheses in the goal
          className={twMerge(
            'mr-1 flex h-6 min-w-6 shrink-0 cursor-pointer items-center justify-center',
            'rounded border border-(--text) text-xs text-gray-400 hover:text-primary',
          )}
          title={t('inventory.insert', { name: tile.displayName })}
          aria-label={t('inventory.insert', { name: tile.displayName })}
          // TODO: insert the name into the input line
          onClick={() => {}}
        >
          <FontAwesomeIcon icon={faReply} />
        </button>
      )}
    </div>
  )
}
