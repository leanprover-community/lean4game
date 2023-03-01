import * as React from 'react';
import { useState, useEffect } from 'react';
import './inventory.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faLock, faLockOpen, faBook, faHammer, faBan } from '@fortawesome/free-solid-svg-icons'
import Markdown from './Markdown';
import { useLoadDocQuery } from '../state/api';

function Inventory({ tactics, lemmas, definitions } :
  {lemmas: {name: string, locked: boolean, disabled: boolean}[],
  tactics: {name: string, locked: boolean, disabled: boolean}[],
  definitions: {name: string, locked: boolean, disabled: boolean}[]}) {

  const [docName, setDocName] = useState(null)
  const [docType, setDocType] = useState(null)


  return (
    <div className="inventory">
      <h2>Tactics</h2>
      <div className="inventory-list">
        { tactics.map(tac =>
           <InventoryItem key={tac.name} showDoc={() => {setDocName(tac.name); setDocType("Tactic")}}
             name={tac.name} locked={tac.locked} disabled={tac.disabled} />) }
      {/* TODO: Click on Tactic: show info
        TODO: click on paste icon -> paste into command line */}
      </div>

      <h2>Definitions</h2>
      <div className="inventory-list">
        { definitions.map(def =>
            <InventoryItem key={def.name} showDoc={() => {setDocName(def.name); setDocType("Definition")}}
              name={def.name} locked={def.locked} disabled={def.disabled} />) }
      </div>

      <h2>Lemmas</h2>
      <div className="inventory-list">
        { lemmas.map(lem =>
            <InventoryItem key={lem.name} showDoc={() => {setDocName(lem.name); setDocType("Lemma")}}
              name={lem.name} locked={lem.locked} disabled={lem.disabled} />) }
      </div>

      {docName && <Documentation name={docName} type={docType} />}
    </div>
  )
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
