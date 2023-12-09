import * as React from 'react';
import { useState, useEffect } from 'react';
import '../css/inventory.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faLock, faBan } from '@fortawesome/free-solid-svg-icons'
import { GameIdContext } from '../app';
import Markdown from './markdown';
import { useLoadDocQuery, InventoryTile, LevelInfo, InventoryOverview, useLoadInventoryOverviewQuery, WorldOverview } from '../state/api';
import { selectDifficulty, selectInventory } from '../state/progress';
import { store } from '../state/store';
import { useSelector } from 'react-redux';

export function Inventory({levelInfo, openDoc, enableAll=false} :
  {
    levelInfo: LevelInfo|InventoryOverview,
    openDoc: (props: {name: string, type: string}) => void,
    enableAll?: boolean,
  }) {

  return (
    <div className="inventory">
    {/* TODO: Click on Tactic: show info
      TODO: click on paste icon -> paste into command line */}
      <h2>Tactics</h2>
      {levelInfo?.tactics &&
        <InventoryList items={levelInfo?.tactics} docType="Tactic" openDoc={openDoc} enableAll={enableAll}/>
      }
      <h2>Definitions</h2>
      {levelInfo?.definitions &&
        <InventoryList items={levelInfo?.definitions} docType="Definition" openDoc={openDoc} enableAll={enableAll}/>
      }
      <h2>Theorems</h2>
      {levelInfo?.lemmas &&
        <InventoryList items={levelInfo?.lemmas} docType="Lemma" openDoc={openDoc} defaultTab={levelInfo?.lemmaTab} level={levelInfo} enableAll={enableAll}/>
      }
    </div>
  )
}

export function OverviewInventory({data, openDoc, enableAll=false, showOverview=true} :
  {
    data: WorldOverview[],
    openDoc: (props: {name: string, type: string}) => void,
    enableAll?: boolean,
    showOverview?: boolean
  }) {

  const gameId = React.useContext(GameIdContext)
  const difficulty = useSelector(selectDifficulty(gameId))
  const [tab, setTab] = useState<string>()
  let inv: string[] = selectInventory(gameId)(store.getState())

  let levelInfo : InventoryOverview = {
    tactics : data ? data.map(world => (world.tactics.map(tile => inv.includes(tile.name) ? {...tile, locked: false} : tile))).flat() : [],
    lemmas : data ? data.map(world => (world.lemmas.map(tile => inv.includes(tile.name) ? {...tile, locked: false} : tile))).flat() : [],
    definitions : data ? data.map(world => (world.definitions.map(tile => inv.includes(tile.name) ? {...tile, locked: false} : tile))).flat() : [],
    lemmaTab: null,
  }

  return (
    <>
      <Inventory levelInfo={levelInfo} openDoc={openDoc} enableAll={enableAll}/>
      {showOverview &&
        <div className="inventory">
          {data && <>
            <h2>Overviews</h2>
            <div className="tab-bar">
              {data.map(world => {
                return <div key={`category-${world.world}`} className={`tab ${world.world == tab ? "active": ""}`} onClick={() => { setTab((tab == world.world) ? null : world.world) }}>{world.world}</div>
              })}
            </div>
            <div className="inventory-list">
              {/* TODO: a bit hacky, do we need to redesign inventory completely and provide it in a better order? */}
              {data.map(world => {
                if (world.world == tab) {
                  return [
                    ...world.tactics.map(item => {
                      return <InventoryItem
                        key={`${world.world}-${item.name}`}
                        showDoc={() => {openDoc({name: item.name, type: 'Tactic'})}}
                        name={item.name} displayName={item.displayName}
                        locked={difficulty > 0 ? !inv.includes(item.name) : false}
                        disabled={item.disabled} newly={false} enableAll={enableAll} />
                    }),
                    ...world.lemmas.map(item => {
                      return <InventoryItem
                        key={`${world.world}-${item.name}`}
                        showDoc={() => {openDoc({name: item.name, type: 'Lemma'})}}
                        name={item.name} displayName={item.displayName}
                        locked={difficulty > 0 ? item.locked : false}
                        disabled={item.disabled} newly={false} enableAll={enableAll} />
                    }),
                    ...world.definitions.map(item => {
                      return <InventoryItem
                        key={`${world.world}-${item.name}`}
                        showDoc={() => {openDoc({name: item.name, type: 'Definition'})}}
                        name={item.name} displayName={item.displayName}
                        locked={difficulty > 0 ? item.locked : false}
                        disabled={item.disabled} newly={false} enableAll={enableAll} />
                    })
                  ]
                }
              })}
            </div>
          </>}
        </div>
      }
    </>

  )
}

function InventoryList({items, docType, openDoc, defaultTab=null, level=undefined, enableAll=false} :
  {
    items: InventoryTile[],
    docType: string,
    openDoc(props: {name: string, type: string}): void,
    defaultTab? : string,
    level? : LevelInfo|InventoryOverview,
    enableAll?: boolean,
  }) {
  // TODO: `level` is only used in the `useEffect` below to check if a new level has
  // been loaded. Is there a better way to observe this?

  const gameId = React.useContext(GameIdContext)

  const difficulty = useSelector(selectDifficulty(gameId))

  const categorySet = new Set<string>()
  for (let item of items) {
    categorySet.add(item.category)
  }
  const categories = Array.from(categorySet).sort()

  const [tab, setTab] = useState(defaultTab)

  // Add inventory items from local store as unlocked.
  // Items are unlocked if they are in the local store, or if the server says they should be
  // given the dependency graph. (OR-connection) (TODO: maybe add different logic for different
  // modi)
  let inv: string[] = selectInventory(gameId)(store.getState())
  let modifiedItems : InventoryTile[] = items.map(tile => inv.includes(tile.name) ? {...tile, locked: false} : tile)

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
          <div key={`category-${cat}`} className={`tab ${cat == (tab ?? categories[0]) ? "active": ""}`}
            onClick={() => { setTab(cat) }}>{cat}</div>)}
      </div>}
    <div className="inventory-list">
      {[...modifiedItems].sort(
          // For lemas, sort entries `available > disabled > locked`
          // otherwise alphabetically
          (x, y) => +(docType == "Lemma") * (+x.locked - +y.locked || +x.disabled - +y.disabled) || x.displayName.localeCompare(y.displayName)
        ).filter(item => !item.hidden && ((tab ?? categories[0]) == item.category)).map((item, i) => {
            return <InventoryItem key={`${item.category}-${item.name}`}
              showDoc={() => {openDoc({name: item.name, type: docType})}}
              name={item.name} displayName={item.displayName} locked={difficulty > 0 ? item.locked : false}
              disabled={item.disabled} newly={item.new} enableAll={enableAll}/>
        })
      }
    </div>
    </>
}

function InventoryItem({name, displayName, locked, disabled, newly, showDoc, enableAll=false}) {
  const icon = locked ? <FontAwesomeIcon icon={faLock} /> :
               disabled ? <FontAwesomeIcon icon={faBan} /> : ""
  const className = locked ? "locked" : disabled ? "disabled" : newly ? "new" : ""
  const title = locked ? "Not unlocked yet" :
                disabled ? "Not available in this level" : ""

  const handleClick = () => {
    if (enableAll || !locked) {
      showDoc()
    }
  }

  return <div className={`item ${className}${enableAll ? ' enabled' : ''}`} onClick={handleClick} title={title}>{icon} {displayName}</div>
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

/** The panel (on the welcome page) showing the user's inventory with tactics, definitions, and lemmas */
export function InventoryPanel({levelInfo, visible = true}) {
  const gameId = React.useContext(GameIdContext)

  // The inventory is overlayed by the doc entry of a clicked item
  const [inventoryDoc, setInventoryDoc] = useState<{name: string, type: string}>(null)
  // Set `inventoryDoc` to `null` to close the doc
  function closeInventoryDoc() {setInventoryDoc(null)}

  return <div className={`column inventory-panel ${visible ? '' : 'hidden'}`}>
    {inventoryDoc ?
      <Documentation name={inventoryDoc.name} type={inventoryDoc.type} handleClose={closeInventoryDoc}/>
      :
      <Inventory levelInfo={levelInfo} openDoc={setInventoryDoc} enableAll={true}/>
    }
  </div>
}

/** The panel (on the welcome page) showing the user's inventory with tactics, definitions, and lemmas */
export function InventoryOverviewPanel({data, visible = true, showOverview=true} : {data : WorldOverview[], visible?: boolean, showOverview?: boolean}) {
  const gameId = React.useContext(GameIdContext)

  // The inventory is overlayed by the doc entry of a clicked item
  const [inventoryDoc, setInventoryDoc] = useState<{name: string, type: string}>(null)
  // Set `inventoryDoc` to `null` to close the doc
  function closeInventoryDoc() {setInventoryDoc(null)}

  return <div className={`column inventory-panel ${visible ? '' : 'hidden'}`}>
    {inventoryDoc ?
      <Documentation name={inventoryDoc.name} type={inventoryDoc.type} handleClose={closeInventoryDoc}/>
      :
      <OverviewInventory data={data} openDoc={setInventoryDoc} enableAll={true} showOverview={showOverview}/>
    }
  </div>
}
