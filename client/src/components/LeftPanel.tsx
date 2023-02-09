import * as React from 'react';
import { useState, useEffect } from 'react';
import './inventory.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faLock, faLockOpen, faBook, faHammer, faBan } from '@fortawesome/free-solid-svg-icons'
import Markdown from './Markdown';

function LeftPanel({ tactics, lemmas } :
  {lemmas: {name: string, locked: boolean, disabled: boolean}[],
   tactics: {name: string, locked: boolean, disabled: boolean}[]}) {

  return (
    <>
    <div className="inventory">
      { tactics.map(tac => <InventoryItem name={tac.name} locked={tac.locked} disabled={tac.disabled} />) }
    {/* TODO: Click on Tactic: show info
      TODO: click on paste icon -> paste into command line */}
    </div>

    <div className="inventory">
      { lemmas.map(lem => <InventoryItem name={lem.name} locked={lem.locked} disabled={lem.disabled} />) }
    </div>
    </>
  )
}

function InventoryItem({name, locked, disabled}) {
  const icon = locked ? <FontAwesomeIcon icon={faLock} /> :
               disabled ? <FontAwesomeIcon icon={faBan} /> : ""
  const className = locked ? "locked" : disabled ? "disabled" : ""
  return <div className={`item ${className}`}>{icon} {name}</div>
}

export default LeftPanel;
