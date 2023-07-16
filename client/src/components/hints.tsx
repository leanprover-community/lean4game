import { GameHint } from "./infoview/rpc_api";
import * as React from 'react';
import Markdown from './markdown';

export function Hint({hint, step, selected, toggleSelection} : {hint: GameHint, step: number, selected: number, toggleSelection: any}) {
  return <div className={`message information step-${step}` + (step == selected ? ' selected' : '')} onClick={toggleSelection}>
    <Markdown>{hint.text}</Markdown>
  </div>
}

export function AdditionalHint({hint, step, selected, toggleSelection} : {hint: GameHint, step: number, selected: number, toggleSelection: any}) {
  return <div className={`message warning step-${step}` + (step == selected ? ' selected' : '')} onClick={toggleSelection}>
    <Markdown>{hint.text}</Markdown>
  </div>
}

export function Hints({hints, showHidden, step, selected, toggleSelection} : {hints: GameHint[], showHidden: boolean, step: number, selected: number, toggleSelection: any}) {

  const openHints = hints.filter(hint => !hint.hidden)
  const hiddenHints = hints.filter(hint => hint.hidden)

  return <>
    {openHints.map(hint => <Hint hint={hint} step={step} selected={selected} toggleSelection={toggleSelection}/>)}
    {showHidden && hiddenHints.map(hint => <AdditionalHint hint={hint} step={step} selected={selected} toggleSelection={toggleSelection}/>)}
  </>
}
