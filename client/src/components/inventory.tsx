import * as React from 'react'
import { useState, useEffect, createContext, useContext } from 'react';
import '../css/inventory.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faLock, faBan, faCheck, faXmark } from '@fortawesome/free-solid-svg-icons'
import { faClipboard } from '@fortawesome/free-regular-svg-icons'
import { useLoadDocQuery, InventoryTile, useLoadInventoryOverviewQuery, useLoadLevelQuery } from '../state/api';
import { changedInventory, selectDifficulty, selectInventory } from '../state/progress';
import { store } from '../state/store';
import { useSelector } from 'react-redux';
import { useTranslation } from 'react-i18next';
import { t } from 'i18next';
import { NavButton } from './navigation';
import { LoadingIcon, Markdown } from './utils';
import { GameIdContext } from '../state/context';
import { useAppDispatch } from '../hooks';


/** Context which manages the inventory */
const InventoryContext = createContext<{
  theoremTab: string,
  setTheoremTab: React.Dispatch<React.SetStateAction<string>>,
  categoryTab: "tactic"|"theorem"|"definition",
  setCategoryTab: React.Dispatch<React.SetStateAction<"tactic"|"theorem"|"definition">>,
  docTile: InventoryTile,
  setDocTile: React.Dispatch<React.SetStateAction<InventoryTile>>
}>({
  theoremTab: null,
  setTheoremTab: () => {},
  categoryTab: "tactic",
  setCategoryTab: () => {},
  docTile: null,
  setDocTile: () => {}
})


/**
 */
function InventoryItem({item, name, displayName, locked, disabled, newly, showDoc } :
    { item: InventoryTile,
      name: any,
      displayName: any,
      locked: any,
      disabled: any,
      newly: any,
      showDoc: any
    }) {
  const icon = locked ? <FontAwesomeIcon icon={faLock} /> :
               disabled ? <FontAwesomeIcon icon={faBan} /> : <></>
  const className = locked ? "locked" : disabled ? "disabled" : newly ? "new" : ""
  // Note: This is somewhat a hack as the statement of theorems comes currently in the form
  // `Namespace.statement_name (x y : Nat) : some type`
  const title = locked ? t("Not unlocked yet") :
                disabled ? t("Not available in this level") : (item.altTitle ? item.altTitle.substring(item.altTitle.indexOf(' ') + 1) : '')

  const { gameId, worldId, levelId } = React.useContext(GameIdContext)
  const difficulty = useSelector(selectDifficulty(gameId))

  // local state to show checkmark after pressing the copy button
  const [copied, setCopied] = useState(false)

  const handleClick = () => {
    // if ((difficulty == 0) || !locked) {
      showDoc()
    // }
  }

  const copyItemName = (ev) => {
    navigator.clipboard.writeText(displayName)
    setCopied(true)
    setInterval(() => {
      setCopied(false)
    }, 3000);
    ev.stopPropagation()
  }

  return <div className={`item ${className}` +
      `${(difficulty == 0) ? ' enabled' : ''}` +
      `${item.world == worldId && item.level == levelId - 1 ? ' recent' : ''}` +
      `${item.world == worldId && item.level < levelId ? ' current-world' : ''}` } onClick={handleClick} title={title}>
    {icon} {displayName}
    <div className="copy-button" onClick={copyItemName}>
      {copied ? <FontAwesomeIcon icon={faCheck} /> : <FontAwesomeIcon icon={faClipboard} />}
    </div>
  </div>
}


function InventoryList({ items, tab=null, setTab=()=>{} } :
  {
    items: InventoryTile[],
    tab?: string,
    setTab?: React.Dispatch<React.SetStateAction<string>>
  }) {

  const { gameId, worldId, levelId } = React.useContext(GameIdContext)
  const { setDocTile, categoryTab, setCategoryTab } = useContext(InventoryContext)

  const difficulty = useSelector(selectDifficulty(gameId))

  const inventory: string[] = selectInventory(gameId)(store.getState())

  const [categories, setCategories] = useState<Array<string>>([])
  const [modifiedItems, setModifiedItems] = useState<Array<InventoryTile>>([])
  const [currentWorldItems, setCurrentWorldItems] = useState<Array<InventoryTile>>([])


  useEffect(() => {
    const categorySet = new Set<string>()

    if (!items) {return}
    for (let item of items) {
      categorySet.add(item.category)
    }
    setCategories(Array.from(categorySet).sort())

    // Add inventory items from local store as unlocked.
    // Items are unlocked if they are in the local store, or if the server says they should be
    // given the dependency graph. (OR-connection) (TODO: maybe add different logic for different
    // modi)
    let _modifiedItems : InventoryTile[] = items?.map(tile => inventory.includes(tile.name) ? {...tile, locked: false} : tile)
    setModifiedItems(_modifiedItems)
    // Item(s) proved in the preceeding level
    setCurrentWorldItems(_modifiedItems.filter(x => x.world == worldId && x.level < levelId))
    // setRecentItems(_modifiedItems.filter(x => x.world == worldId && x.level == levelId - 1))

  }, []) // TODO: had `items, inventory`

  return <>
    { categories.length > 1 &&
      <div className="tab-bar">
        {categories.map((cat) => {
          let hasNew = modifiedItems.filter(item => item.new && (cat == item.category)).length > 0
          return <div key={`category-${cat}`} className={`tab${cat == (tab ?? categories[0]) ? " active": ""}${hasNew ? ' new': ''}${currentWorldItems.map(x => x.category).includes(cat) ? ' recent': ''}`}
            onClick={() => { setTab(cat) }}>{cat}</div>})}
      </div>}
    <div className="inventory-list">
      {[...modifiedItems].sort(
          // alternative approach:
          // // For theorems, sort entries `available > disabled > locked`
          // // otherwise alphabetically
          // (x, y) => +(categoryTab == "theorem") * (+x.locked - +y.locked || +x.disabled - +y.disabled) || x.displayName.localeCompare(y.displayName)

          // sort alphabetically
          (x, y) => x.displayName.localeCompare(y.displayName)
        ).filter(item => !item.hidden && ((tab ?? categories[0]) == item.category)).map((item, i) => {
            return <InventoryItem key={`${item.category}-${item.name}`}
              item={item}
              showDoc={() => {setDocTile(item)}}
              name={item.name} displayName={item.displayName} locked={difficulty > 0 ? item.locked : false}
              disabled={item.disabled}
              newly={item.new} />
        })
      }
    </div>
    </>
}



/** The `Inventory` shows all items present in the game sorted by item type. */
export function Inventory () {
  const { t } = useTranslation()

  const { gameId, worldId, levelId } = React.useContext(GameIdContext)
  const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})

  let { theoremTab, setTheoremTab, categoryTab, setCategoryTab } = useContext(InventoryContext)

  /** Helper function to find if a list of tiles comprises any new elements. */
  function containsNew(tiles: InventoryTile[]) {
    return tiles?.filter(item => item.new).length > 0
  }

  return (
    <div className="inventory">
      { levelInfo.data ? <>
      <div className="tab-bar major">
        <div className={`tab${(categoryTab == "theorem") ? " active": ""}${containsNew(levelInfo.data?.theorems) ? " new" : ""}`} onClick={() => { setCategoryTab("theorem") }}>{t("Theorems")}</div>
        <div className={`tab${(categoryTab == "tactic") ? " active": ""}${containsNew(levelInfo.data?.tactics) ? " new" : ""}`} onClick={() => { setCategoryTab("tactic") }}>{t("Tactics")}</div>
        <div className={`tab${(categoryTab == "definition") ? " active": ""}${containsNew(levelInfo.data?.definitions) ? " new" : ""}`} onClick={() => { setCategoryTab("definition") }}>{t("Definitions")}</div>
      </div>
      { (categoryTab == "theorem") &&
        <InventoryList items={levelInfo.data?.theorems} tab={theoremTab} setTab={setTheoremTab} />
      }
      { (categoryTab == "tactic") &&
        <InventoryList items={levelInfo.data?.tactics} />
      }
      { (categoryTab == "definition") &&
        <InventoryList items={levelInfo.data?.definitions} />
      }
    </> : <LoadingIcon /> }
    </div>
  )
}

/** The `documentation` */
export function Documentation() {
  const dispatch = useAppDispatch()
  const { gameId } = useContext(GameIdContext)
  const difficulty = useSelector(selectDifficulty(gameId))

  // const docEntry = useLoadDocQuery({game: gameId, type: type, name: name})
  let { docTile, setDocTile } = useContext(InventoryContext)

  const docEntry = useLoadDocQuery({game: gameId, name: docTile.name})
  let inv: string[] = selectInventory(gameId)(store.getState())

  // Set `inventoryDoc` to `null` to close the doc
  function closeInventoryDoc() { setDocTile(null) }

  return <div className="documentation">
    <NavButton
      icon={faXmark}
      onClick={closeInventoryDoc}
      inverted={true} />
    { difficulty == 1 && docTile.locked &&
      <NavButton
        icon={faLock}
        title={t("Unlock this item!")}
        onClick={() => {
          console.log(`Adding '${docTile.name}' to the inventory.`)
          dispatch(changedInventory({ game: gameId, inventory: [...inv, docTile.name] }))
          closeInventoryDoc() // note: closing seems better than keeping it open without the lock disappearing
        }}
        className="lock"
        inverted={true} />
    }
    <h1 className="doc">{docTile.displayName}</h1>
    <p><code>{docEntry.data?.statement}</code></p>
    <Markdown>{t(docEntry.data?.content, {ns: gameId})}</Markdown>
    {/* TODO: The condition below should be updated so that the section
    is displayed whenever it's non-empty. */}
    {docTile.proven && <>
        <h2>Further details</h2>
        <ul>
          {docTile.proven && <li>Proven in: <a href={`#/${gameId}/world/${docTile.world}/level/${docTile.level}`}>{docTile.world} level {docTile.level}</a></li>}
        </ul>
      </>
    }

  </div>
}

/** The panel showing the user's inventory with tactics, definitions, and theorems */
export function InventoryPanel({visible = true}) {
  const {gameId, worldId, levelId} = React.useContext(GameIdContext)
  const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})
  const inventory = useLoadInventoryOverviewQuery({game: gameId})

  const [theoremTab, setTheoremTab] = useState<string>(null)
  const [categoryTab, setCategoryTab] = useState<"tactic"|"theorem"|"definition">('tactic')
  // The inventory is overlayed by the doc entry of a clicked item
  const [docTile, setDocTile] = useState<InventoryTile>(null)

  useEffect(() => {
    // If the level specifies `TheoremTab "Nat"`, we switch to this tab on loading.
    // `defaultTab` is `null` or `undefined` otherwise, in which case we don't want to switch.
    if (levelInfo?.data?.theoremTab) {
      setTheoremTab(levelInfo?.data?.theoremTab)
    }}, [levelInfo])

  return <div className={`column inventory-panel ${visible ? '' : 'hidden'}`}>
    <InventoryContext.Provider value={{theoremTab, setTheoremTab, categoryTab, setCategoryTab, docTile, setDocTile }}>
    {docTile ?
      <Documentation />
      :
      <Inventory />
    }
    </InventoryContext.Provider>
  </div>
}

// HERE: next up: locked items should not be disabled!
