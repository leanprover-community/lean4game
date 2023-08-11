import { GameHint } from "./infoview/rpc_api";
import * as React from 'react';
import Markdown from './markdown';

export function Hint({hint, step, selected, toggleSelection, lastLevel} : {hint: GameHint, step: number, selected: number, toggleSelection: any, lastLevel?: boolean}) {
  return <div className={`message information step-${step}` + (step == selected ? ' selected' : '') + (lastLevel ? ' recent' : '')} onClick={toggleSelection}>
    <Markdown>{hint.text}</Markdown>
  </div>
}

export function HiddenHint({hint, step, selected, toggleSelection, lastLevel} : {hint: GameHint, step: number, selected: number, toggleSelection: any, lastLevel?: boolean}) {
  return <div className={`message warning step-${step}` + (step == selected ? ' selected' : '') + (lastLevel ? ' recent' : '')} onClick={toggleSelection}>
    <Markdown>{hint.text}</Markdown>
  </div>
}

export function Hints({hints, showHidden, step, selected, toggleSelection, lastLevel} : {hints: GameHint[], showHidden: boolean, step: number, selected: number, toggleSelection: any, lastLevel?: boolean}) {

  const openHints = hints.filter(hint => !hint.hidden)
  const hiddenHints = hints.filter(hint => hint.hidden)

  // TODO: Should not use index as key.
  return <>
    {openHints.map((hint, j) => <Hint key={`hint-${step}-${j}`} hint={hint} step={step} selected={selected} toggleSelection={toggleSelection} lastLevel={lastLevel} />)}
    {showHidden && hiddenHints.map((hint, j) => <HiddenHint key={`hidden-hint-${step}-${j}`} hint={hint} step={step} selected={selected} toggleSelection={toggleSelection} lastLevel={lastLevel} />)}
  </>
}

export function DeletedHint({hint} : {hint: GameHint}) {
  return <div className="message information deleted-hint">
    <Markdown>{hint.text}</Markdown>
  </div>
}

export function DeletedHints({hints} : {hints: GameHint[]}) {

  const openHints = hints.filter(hint => !hint.hidden)
  const hiddenHints = hints.filter(hint => hint.hidden)

  // TODO: Should not use index as key.
  return <>
    {openHints.map((hint, i) => <DeletedHint key={`deleted-hint-${i}`} hint={hint} />)}
    {hiddenHints.map((hint, i) => <DeletedHint key={`deleted-hidden-hint-${i}`} hint={hint}/>)}
  </>
}
