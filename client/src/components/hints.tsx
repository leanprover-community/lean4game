import { GameHint } from "./infoview/rpc_api";
import * as React from 'react';
import Markdown from './markdown';
import { ProofStep } from "./infoview/context";

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

/** Filter hints to not show consequtive identical hints twice.
 *
 * This function takes a `ProofStep[]` and extracts the hints in form of an
 * element of type `GameHint[][]` where it removes hints that are identical to hints
 * appearing in the previous step.
 *
 * This effectively means we prevent consequtive identical hints from being shown.
 */
export function filterHints(proof: ProofStep[]): GameHint[][] {
  return proof.map((step, i) => {
    if (i == 0){
      return step.hints
    } else {
      // TODO: Writing all fields explicitely is somewhat fragile to changes, is there a
      // good way to shallow-compare objects?
      return step.hints.filter((hint) => proof[i-1].hints.find((x) => (x.text == hint.text && x.hidden == hint.hidden)) === undefined)
    }
  })
}
