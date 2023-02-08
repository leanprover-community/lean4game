import * as React from 'react';
import { useState, useEffect } from 'react';
import './inventory.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faLock, faLockOpen, faBook, faHammer, faBan } from '@fortawesome/free-solid-svg-icons'
import Markdown from './Markdown';


function LeftPanel({ tactics, inventory, showSidePanel, setShowSidePanel }) {

  return (
    <>
    <div className="tactic-inventory">
      {  tactics.map (({name, locked, disabled}) => {
        const icon = locked ? <FontAwesomeIcon icon={faLock} /> :
                     disabled ? <FontAwesomeIcon icon={faBan} /> : ""
        const className = locked ? "locked" : disabled ? "disabled" : ""
        return <div className={`tactic ${className}`}>{icon} {name}</div>
    })}
    {/* TODO: Click on Tactic: show info
      TODO: click on paste icon -> paste into command line */}
    </div>
    </>
  )
}

export default LeftPanel;
