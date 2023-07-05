import { GameHint } from "./infoview/rpc_api";
import * as React from 'react';
import Markdown from './markdown';

export function Hint({hint} : {hint: GameHint}) {
  return <div className="message info"><Markdown>{hint.text}</Markdown></div>
}

export function Hints({hints, showHidden} : {hints: GameHint[], showHidden: boolean}) {

  const openHints = hints.filter(hint => !hint.hidden)
  const hiddenHints = hints.filter(hint => hint.hidden)

  return <>
    {openHints.map(hint => <Hint hint={hint} />)}
    {showHidden && hiddenHints.map(hint => <Hint hint={hint} />)}
  </>
}
