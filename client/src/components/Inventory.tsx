import * as React from 'react';
import { useState, useEffect } from 'react';
import './inventory.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faLock, faLockOpen, faBook, faHammer, faBan } from '@fortawesome/free-solid-svg-icons'
import Markdown from './Markdown';
import { useLoadDocQuery, ComputedInventoryItem, LevelInfo } from '../state/api';
import { GameIdContext } from '../App';

export function Inventory({levelInfo, setInventoryDoc } :
  {
    levelInfo: LevelInfo,
    setInventoryDoc: (inventoryDoc: {name: string, type: string}) => void,
  }) {

  function openDoc(name, type) {
    setInventoryDoc({name, type})
  }

  return (
    <div className="inventory">
    {/* TODO: Click on Tactic: show info
      TODO: click on paste icon -> paste into command line */}
      <h2>Tactics</h2>
      <InventoryList items={levelInfo?.tactics} docType="Tactic" openDoc={openDoc} />

      <h2>Definitions</h2>
      <InventoryList items={levelInfo?.definitions} docType="Definition" openDoc={openDoc} />

      <h2>Lemmas</h2>
      <InventoryList items={levelInfo?.lemmas} docType="Lemma" openDoc={openDoc}
        defaultTab={levelInfo?.lemmaTab} level={levelInfo}/>
    </div>
  )
}

function InventoryList({items, docType, openDoc, defaultTab=null, level=undefined} :
  {
    items: ComputedInventoryItem[],
    docType: string,
    openDoc(name: string, type: string): void,
    defaultTab? : string,
    level? : LevelInfo,
  }) {
  // TODO: `level` is only used in the `useEffect` below to check if a new level has
  // been loaded. Is there a better way to observe this?

  const categorySet = new Set<string>()
  for (let item of items) {
    categorySet.add(item.category)
  }
  const categories = Array.from(categorySet).sort()

  const [tab, setTab] = useState(defaultTab);

  useEffect(() => {
    // If the level specifies `LemmaTab "Nat"`, we switch to this tab on loading.
    // `defaultTab` is `null` or `undefined` otherwise, in which case we don't want to switch.
    if (defaultTab) {
      setTab(defaultTab)
    }}, [level])

  return <>
    {categories.length > 1 &&
      <div className="tab-bar">
        {categories.map((cat) =>
          <div className={`tab ${cat == (tab ?? categories[0]) ? "active": ""}`} onClick={() => { setTab(cat) }}>{cat}</div>)}
      </div>}
    <div className="inventory-list">
    { [...items].sort(
      // Sort entries `available > disabled > locked`.
      (x, y) => +x.locked - +y.locked || +x.disabled - +y.disabled
    ).map(item => {
        if ((tab ?? categories[0]) == item.category) {
          return <InventoryItem key={item.name} showDoc={() => {openDoc(item.name, docType)}}
            name={item.name} displayName={item.displayName} locked={item.locked}
            disabled={item.disabled} newly={item.new}/>
        }
      }) }
    </div>
    </>
}

function InventoryItem({name, displayName, locked, disabled, newly, showDoc}) {
  const icon = locked ? <FontAwesomeIcon icon={faLock} /> :
               disabled ? <FontAwesomeIcon icon={faBan} /> : ""
  const className = newly ? "new" : "old"
  // const className = locked ? "locked" : disabled ? "disabled" : newly ? "new" : ""
  const title = locked ? "Not unlocked yet" :
                disabled ? "Not available in this level" : ""

  const handleClick = () => {
    if (!locked && !disabled) {
      showDoc()
    }
  }

  return <div className={`item ${className}`} onClick={handleClick} title={title}>{icon} {displayName}</div>
}

export function Documentation({name, type}) {
  const gameId = React.useContext(GameIdContext)
  const doc = useLoadDocQuery({game: gameId, type: type, name: name})

  return <>
    <h2 className="doc">{doc.data?.displayName}</h2>
    <Markdown>{doc.data?.text}</Markdown>
  </>
}
