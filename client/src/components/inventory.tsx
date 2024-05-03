import * as React from 'react';
import { useState, useEffect } from 'react';
import '../css/inventory.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faLock, faBan, faCheck } from '@fortawesome/free-solid-svg-icons'
import { faClipboard } from '@fortawesome/free-regular-svg-icons'
import { GameIdContext } from '../app';
import Markdown from './markdown';
import { useLoadDocQuery, InventoryTile, LevelInfo, InventoryOverview, useLoadInventoryOverviewQuery } from '../state/api';
import { selectDifficulty, selectInventory } from '../state/progress';
import { store } from '../state/store';
import { useSelector } from 'react-redux';
import { useTranslation } from 'react-i18next';
import { t } from 'i18next';
import { WorldLevelIdContext } from './infoview/context';

export function Inventory({levelInfo, openDoc, lemmaTab, setLemmaTab, enableAll=false} :
  {
    levelInfo: LevelInfo|InventoryOverview,
    openDoc: (props: {name: string, type: string}) => void,
    lemmaTab: any,
    setLemmaTab: any,
    enableAll?: boolean,
  }) {
  const { t } = useTranslation()

  // TODO: this state should be preserved when loading a different level.
  const [tab, setTab] = useState<"tactic"|"theorem"|"definition">("theorem")

  let newTheorems = levelInfo?.lemmas?.filter(item => item.new).length > 0
  let newTactics = levelInfo?.tactics?.filter(item => item.new).length > 0
  let newDefinitions = levelInfo?.definitions?.filter(item => item.new).length > 0

  return (
    <div className="inventory">
      <div className="tab-bar major">
        <div className={`tab${(tab == "theorem") ? " active": ""}${newTheorems ? " new" : ""}`} onClick={() => { setTab("theorem") }}>{t("Theorems")}</div>
        <div className={`tab${(tab == "tactic") ? " active": ""}${newTactics ? " new" : ""}`} onClick={() => { setTab("tactic") }}>{t("Tactics")}</div>
        <div className={`tab${(tab == "definition") ? " active": ""}${newDefinitions ? " new" : ""}`} onClick={() => { setTab("definition") }}>{t("Definitions")}</div>
      </div>
      { (tab == "theorem") && levelInfo?.lemmas &&
        <InventoryList items={levelInfo?.lemmas} docType="Lemma" openDoc={openDoc} level={levelInfo} enableAll={enableAll} tab={lemmaTab} setTab={setLemmaTab}/>
      }
      { (tab == "tactic") && levelInfo?.tactics &&
        <InventoryList items={levelInfo?.tactics} docType="Tactic" openDoc={openDoc} enableAll={enableAll}/>
      }
      { (tab == "definition") && levelInfo?.definitions &&
        <InventoryList items={levelInfo?.definitions} docType="Definition" openDoc={openDoc} enableAll={enableAll}/>
      }
    </div>
  )
}

function InventoryList({items, docType, openDoc, tab=null, setTab=undefined, level=undefined, enableAll=false} :
  {
    items: InventoryTile[],
    docType: string,
    openDoc(props: {name: string, type: string}): void,
    tab?: any,
    setTab?: any,
    level?: LevelInfo|InventoryOverview,
    enableAll?: boolean,
  }) {
  // TODO: `level` is only used in the `useEffect` below to check if a new level has
  // been loaded. Is there a better way to observe this?

  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)

  const difficulty = useSelector(selectDifficulty(gameId))

  const categorySet = new Set<string>()
  for (let item of items) {
    categorySet.add(item.category)
  }
  const categories = Array.from(categorySet).sort()

  // Add inventory items from local store as unlocked.
  // Items are unlocked if they are in the local store, or if the server says they should be
  // given the dependency graph. (OR-connection) (TODO: maybe add different logic for different
  // modi)
  let inv: string[] = selectInventory(gameId)(store.getState())
  let modifiedItems : InventoryTile[] = items.map(tile => inv.includes(tile.name) ? {...tile, locked: false} : tile)

  // Item(s) proved in the preceeding level
  let recentItems = modifiedItems.filter(x => x.world == worldId && x.level == levelId - 1)

  return <>
    {categories.length > 1 &&
      <div className="tab-bar">
        {categories.map((cat) => {
          let hasNew = modifiedItems.filter(item => item.new && (cat == item.category)).length > 0
          return <div key={`category-${cat}`} className={`tab${cat == (tab ?? categories[0]) ? " active": ""}${hasNew ? ' new': ''}${recentItems.map(x => x.category).includes(cat) ? ' recent': ''}`}
            onClick={() => { setTab(cat) }}>{cat}</div>})}
      </div>}
    <div className="inventory-list">
      {[...modifiedItems].sort(
          // For lemas, sort entries `available > disabled > locked`
          // otherwise alphabetically
          (x, y) => +(docType == "Lemma") * (+x.locked - +y.locked || +x.disabled - +y.disabled) || x.displayName.localeCompare(y.displayName)
        ).filter(item => !item.hidden && ((tab ?? categories[0]) == item.category)).map((item, i) => {
            return <InventoryItem key={`${item.category}-${item.name}`}
              item={item}
              showDoc={() => {openDoc({name: item.name, type: docType})}}
              name={item.name} displayName={item.displayName} locked={difficulty > 0 ? item.locked : false}
              disabled={item.disabled}
              recent={recentItems.map(x => x.name).includes(item.name)}
              newly={item.new} enableAll={enableAll} />
        })
      }
    </div>
    </>
}

function InventoryItem({item, name, displayName, locked, disabled, newly, showDoc, recent=false, enableAll=false}) {
  const icon = locked ? <FontAwesomeIcon icon={faLock} /> :
               disabled ? <FontAwesomeIcon icon={faBan} /> : item.st
  const className = locked ? "locked" : disabled ? "disabled" : newly ? "new" : ""
  // Note: This is somewhat a hack as the statement of lemmas comes currently in the form
  // `Namespace.statement_name (x y : Nat) : some type`
  const title = locked ? t("Not unlocked yet") :
                disabled ? t("Not available in this level") : (item.altTitle ? item.altTitle.substring(item.altTitle.indexOf(' ') + 1) : '')

  const [copied, setCopied] = useState(false)

  const handleClick = () => {
    if (enableAll || !locked) {
      showDoc()
    }
  }

  const copyItemName = (ev) => {
    navigator.clipboard.writeText(displayName)
    setCopied(true)
    setInterval(() => {
      setCopied(false)
    }, 3000);
    ev.stopPropagation()
  }

return <div className={`item ${className}${enableAll ? ' enabled' : ''}${recent ? ' recent' : ''}`} onClick={handleClick} title={title}>
    {icon} {displayName}
    <div className="copy-button" onClick={copyItemName}>
      {copied ? <FontAwesomeIcon icon={faCheck} /> : <FontAwesomeIcon icon={faClipboard} />}
    </div>
  </div>
}

export function Documentation({name, type, handleClose}) {
  const gameId = React.useContext(GameIdContext)
  const doc = useLoadDocQuery({game: gameId, type: type, name: name})

  return <div className="documentation">
    <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
    <h1 className="doc">{doc.data?.displayName}</h1>
    <p><code>{doc.data?.statement}</code></p>
    {/* <code>docstring: {doc.data?.docstring}</code> */}
    <Markdown>{t(doc.data?.content, {ns: gameId})}</Markdown>
  </div>
}

/** The panel (on the welcome page) showing the user's inventory with tactics, definitions, and lemmas */
export function InventoryPanel({levelInfo, visible = true}) {
  const gameId = React.useContext(GameIdContext)

  const [lemmaTab, setLemmaTab] = useState(levelInfo?.lemmaTab)

  // The inventory is overlayed by the doc entry of a clicked item
  const [inventoryDoc, setInventoryDoc] = useState<{name: string, type: string}>(null)
  // Set `inventoryDoc` to `null` to close the doc
  function closeInventoryDoc() {setInventoryDoc(null)}

    useEffect(() => {
    // If the level specifies `LemmaTab "Nat"`, we switch to this tab on loading.
    // `defaultTab` is `null` or `undefined` otherwise, in which case we don't want to switch.
    if (levelInfo?.lemmaTab) {
      setLemmaTab(levelInfo?.lemmaTab)
    }}, [levelInfo])

  return <div className={`column inventory-panel ${visible ? '' : 'hidden'}`}>
    {inventoryDoc ?
      <Documentation name={inventoryDoc.name} type={inventoryDoc.type} handleClose={closeInventoryDoc}/>
      :
      <Inventory levelInfo={levelInfo} openDoc={setInventoryDoc} enableAll={true} lemmaTab={lemmaTab} setLemmaTab={setLemmaTab}/>
    }
  </div>
}
