import { GameHint, InteractiveGoalsWithHints, ProofState } from "./infoview/rpc_api";
import * as React from 'react';
import Markdown from './markdown';
import { DeletedChatContext, ProofContext } from "./infoview/context";
import { lastStepHasErrors } from "./infoview/goals";
import { Button } from "./button";

/** Plug-in the variable names in a hint. We do this client-side to prepare
 * for i18n in the future. i.e. one should be able translate the `rawText`
 * and have the variables substituted just before displaying.
 */
function getHintText(hint: GameHint): string {
  if (hint.rawText) {
    // Replace the variable names used in the hint with the ones used by the player
    // variable names are marked like `«{g}»` inside the text.
    return hint.rawText.replace(/«\{(.*?)\}»/, ((_, v) =>
      // `hint.varNames` contains tuples `[oldName, newName]`
      (hint.varNames.find(x => x[0] == v))[1]))
  } else {
    // hints created in the frontend do not have a `rawText`
    // TODO: `hint.text` could be removed in theory.
    return hint.text
  }
}

export function Hint({hint, step, selected, toggleSelection, lastLevel} : {hint: GameHint, step: number, selected: number, toggleSelection: any, lastLevel?: boolean}) {
  return <div className={`message information step-${step}` + (step == selected ? ' selected' : '') + (lastLevel ? ' recent' : '')} onClick={toggleSelection}>
    <Markdown>{getHintText(hint)}</Markdown>
  </div>
}

export function HiddenHint({hint, step, selected, toggleSelection, lastLevel} : {hint: GameHint, step: number, selected: number, toggleSelection: any, lastLevel?: boolean}) {
  return <div className={`message warning step-${step}` + (step == selected ? ' selected' : '') + (lastLevel ? ' recent' : '')} onClick={toggleSelection}>
    <Markdown>{getHintText(hint)}</Markdown>
  </div>
}

export function Hints({hints, showHidden, step, selected, toggleSelection, lastLevel} : {hints: GameHint[], showHidden: boolean, step: number, selected: number, toggleSelection: any, lastLevel?: boolean}) {
  if (!hints) {return <></>}
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
    <Markdown>{getHintText(hint)}</Markdown>
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
 * Hidden hints are not filtered.
 */
export function filterHints(hints: GameHint[], prevHints: GameHint[]): GameHint[] {
  if (!hints) {
    return []}
  else if (!prevHints) {
    return hints }
  else {
    return hints.filter((hint) => hint.hidden ||
    (prevHints.find(x => (x.text == hint.text && x.hidden == hint.hidden)) === undefined)
    )
  }
}


function hasHiddenHints(step: InteractiveGoalsWithHints): boolean {
  return step?.goals[0]?.hints.some((hint) => hint.hidden)
}


export function MoreHelpButton({selected=null} : {selected?: number}) {

  const {proof, setProof} = React.useContext(ProofContext)
  const {deletedChat, setDeletedChat, showHelp, setShowHelp} = React.useContext(DeletedChatContext)

  let k = (selected === null) ? (proof.steps.length - (lastStepHasErrors(proof) ? 2 : 1)) : selected

  const activateHiddenHints = (ev) => {
    // If the last step (`k`) has errors, we want the hidden hints from the
    // second-to-last step to be affected
    if (!(proof.steps.length)) {return}

    // state must not be mutated, therefore we need to clone the set
    let tmp = new Set(showHelp)
    if (tmp.has(k)) {
      tmp.delete(k)
    } else {
      tmp.add(k)
    }
    setShowHelp(tmp)
    console.debug(`help: ${Array.from(tmp.values())}`)
  }

  if (hasHiddenHints(proof.steps[k]) && !showHelp.has(k)) {
    return <Button to="" onClick={activateHiddenHints}>
      Show more help!
    </Button>
  }
}
