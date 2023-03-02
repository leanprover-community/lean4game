import * as React from 'react';
import { useState, useEffect } from 'react';
import './inventory.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faLock, faLockOpen, faBook, faHammer, faBan } from '@fortawesome/free-solid-svg-icons'
import Markdown from './Markdown';
import { useLoadDocQuery, ComputedInventoryItem } from '../state/api';

function Inventory({ tactics, lemmas, definitions } :
  {lemmas: ComputedInventoryItem[],
  tactics: ComputedInventoryItem[],
  definitions: ComputedInventoryItem[]}) {

  const [docName, setDocName] = useState(null)
  const [docType, setDocType] = useState(null)

  function openDoc(name, type) {
    setDocName(name)
    setDocType(type)
  }

  return (
    <div className="inventory">
    {/* TODO: Click on Tactic: show info
      TODO: click on paste icon -> paste into command line */}
      <h2>Tactics</h2>
      <InventoryList items={tactics} docType="Tactic" openDoc={openDoc} />

      <h2>Definitions</h2>
      <InventoryList items={definitions} docType="Definition" openDoc={openDoc} />

      <h2>Lemmas</h2>
      <InventoryList items={lemmas} docType="Lemma" openDoc={openDoc} />

      {docName && <Documentation name={docName} type={docType} />}
    </div>
  )
}

function InventoryList({items, docType, openDoc} : {items: ComputedInventoryItem[], docType: string, openDoc(name: string, type: string): void}) {

  const categorySet = new Set<string>()
  for (let item of items) {
    categorySet.add(item.category)
  }
  const categories = Array.from(categorySet).sort()

  const [tab, setTab] = useState(categories[0]);

  return <>
    {categories.length > 1 &&
      <div className="tab-bar">
        {categories.map((cat) =>
          <div className={`tab ${cat == tab ? "active": ""}`} onClick={() => { setTab(cat) }}>{cat}</div>)}
      </div>}
    <div className="inventory-list">
    { items.map(item => {
        if (tab == item.category) {
          return <InventoryItem key={item.name} showDoc={() => {openDoc(item.name, docType)}}
            name={item.name} locked={item.locked} disabled={item.disabled} />
        }
      }) }
    </div>
    </>
}

function InventoryItem({name, locked, disabled, showDoc}) {
  const icon = locked ? <FontAwesomeIcon icon={faLock} /> :
               disabled ? <FontAwesomeIcon icon={faBan} /> : ""
  const className = locked ? "locked" : disabled ? "disabled" : ""

  const handleClick = () => {
    if (!locked && !disabled) {
      showDoc()
    }
  }

  return <div className={`item ${className}`} onClick={handleClick}>{icon} {name}</div>
}

function Documentation({name, type}) {

  const doc = useLoadDocQuery({type: type, name: name})

  return <>
    <h2 className="doc">{doc.data?.name}</h2>
    <Markdown>{doc.data?.text}</Markdown>
  </>
}

export default Inventory;
