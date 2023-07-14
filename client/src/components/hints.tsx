import { GameHint } from "./infoview/rpc_api";
import * as React from 'react';
import Markdown from './markdown';

export function Hint({hint, selected, toggleSelection} : {hint: GameHint, selected: boolean, toggleSelection: any}) {
  return <div className={"message information" + (selected ? ' selected' : '')} onClick={toggleSelection}>
    <Markdown>{hint.text}</Markdown>
  </div>
}

export function AdditionalHint({hint, selected, toggleSelection} : {hint: GameHint, selected: boolean, toggleSelection: any}) {
  return <div className={"message warning" + (selected ? ' selected' : '')} onClick={toggleSelection}>
    <Markdown>{hint.text}</Markdown>
  </div>
}

export function Hints({hints, showHidden, selected, toggleSelection} : {hints: GameHint[], showHidden: boolean, selected: boolean, toggleSelection: any}) {

  const openHints = hints.filter(hint => !hint.hidden)
  const hiddenHints = hints.filter(hint => hint.hidden)

  return <>
    {openHints.map(hint => <Hint hint={hint} selected={selected} toggleSelection={toggleSelection}/>)}
    {showHidden && hiddenHints.map(hint => <AdditionalHint hint={hint} selected={selected} toggleSelection={toggleSelection}/>)}
  </>
}
