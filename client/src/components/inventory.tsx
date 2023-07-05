import * as React from 'react';
import { useState, useEffect } from 'react';
import './inventory.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faLock, faLockOpen, faBook, faHammer, faBan } from '@fortawesome/free-solid-svg-icons'
import { GameIdContext } from './infoview/context';
import Markdown from './markdown';
import { useLoadDocQuery, InventoryTile, LevelInfo } from '../state/api';

export function Inventory({levelInfo, openDoc } :
  {
    levelInfo: LevelInfo,
    openDoc: (name: string, type: string) => void,
  }) {

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
    items: InventoryTile[],
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
      // For lemas, sort entries `available > disabled > locked`
      // otherwise alphabetically
      (x, y) => +(docType == "Lemma") * (+x.locked - +y.locked || +x.disabled - +y.disabled)
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
  const className = locked ? "locked" : disabled ? "disabled" : newly ? "new" : ""
  const title = locked ? "Not unlocked yet" :
                disabled ? "Not available in this level" : ""

  const handleClick = () => {
    if (!locked) {
      showDoc()
    }
  }

  return <div className={`item ${className}`} onClick={handleClick} title={title}>{icon} {displayName}</div>
}

export function Documentation({name, type, handleClose}) {
  const gameId = React.useContext(GameIdContext)
  const doc = useLoadDocQuery({game: gameId, type: type, name: name})

  return <div className="documentation">
    <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
    <h1 className="doc">{doc.data?.displayName}</h1>
    <p><code>{doc.data?.statement}</code></p>
    {/* <code>docstring: {doc.data?.docstring}</code> */}
    <Markdown>{doc.data?.content}</Markdown>
  </div>
}
