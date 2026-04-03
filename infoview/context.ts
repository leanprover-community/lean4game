/**
 *  @fileOverview This file contains the the react contexts used in the project.
 */
import * as React from 'react';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { InteractiveDiagnostic } from '@leanprover/infoview-api';
import { InteractiveTermGoal,InteractiveGoalsWithHints } from './rpc_api';
import { Preferences, preferencesAtom } from '../client/src/store/preferences-atoms';
import { useAtom } from 'jotai';
import { typewriterContentAtom } from '../client/src/store/editor-atoms';

export const MonacoEditorContext = React.createContext<monaco.editor.IStandaloneCodeEditor>(
  null as any)

export type InfoStatus = 'updating' | 'error' | 'ready';

// /** One step of the proof */
// export type ProofStep = {
//   /** The command in this step */
//   command : string
//   /** List of goals *after* this command */
//   goals: InteractiveGoal[]     // TODO: Add correct type
//   /** Story relevant messages */
//   hints: GameHint[]        // TODO: Add correct type
//   /** Errors and warnings */
//   errors: InteractiveDiagnostic[]       // TODO: Add correct type
// }


// TODO: Do we still need that?
export interface ProofStateProps {
  // pos: DocumentPosition;
  status: InfoStatus;
  messages: InteractiveDiagnostic[];
  goals?: InteractiveGoalsWithHints;
  termGoal?: InteractiveTermGoal;
  error?: string;
  // userWidgets: UserWidgetInstance[];
  // rpcSess: RpcSessionAtPos;
  // triggerUpdate: () => Promise<void>;
}

// export const ProofStateContext = React.createContext<{
//   proofState : ProofStateProps,
//   setProofState: React.Dispatch<React.SetStateAction<ProofStateProps>>
// }>({
//   proofState : {
//     status: 'updating',
//     messages: [],
//     goals: undefined,
//     termGoal: undefined,
//     error: undefined},
//   setProofState: () => {},
// })

export interface IPreferencesContext extends Preferences{
  mobile: boolean, // The variables that actually control the page 'layout' can only be changed through layout.
  setLayout: React.Dispatch<React.SetStateAction<Preferences["layout"]>>;
  setIsSavePreferences: React.Dispatch<React.SetStateAction<Preferences["isSavePreferences"]>>;
  setLanguage: React.Dispatch<React.SetStateAction<Preferences["language"]>>;
}


const SUFFIX_OVERRIDES: Record<string, string> = {
  "induction": "generalizing",
  "left": ".left",
  "rewrite": "←",
  "right": ".right",
  "rw": "←",
}
const PREFIX_OVERRIDES: Record<string, string> = {
  "by_cases": "by_cases this :",
  "contrapose": "contrapose!",
  "have": "have :",
  "obtain": "obtain ⟨⟩ :=",
  "rewrite": "rw []",
  "rw": "rw []",
  "simp": "simp only []",
}
export function useAppendTypewriterInput() {
  const [typewriter, setTypewriter] = useAtom(typewriterContentAtom)
  const [{ isSuggestionsMobileMode }] = useAtom(preferencesAtom)
  return (shiftKey: boolean, suffix: string, isTheorem: boolean, isAssumption: boolean) => {
    if (!isSuggestionsMobileMode && !shiftKey) {
      return false
    }
    // Automagically detect and adjust punctuation for mobile keyboardless usage
    let _typewriter = typewriter.trim()
    if (!typewriter.length) {
      _typewriter = Object.hasOwn(PREFIX_OVERRIDES, suffix) ? PREFIX_OVERRIDES[suffix] : isTheorem ? `rw [${suffix}]` : suffix
      setTypewriter(_typewriter + " ")
      return true
    }
    suffix = !isAssumption && Object.hasOwn(SUFFIX_OVERRIDES, suffix) ? SUFFIX_OVERRIDES[suffix] : suffix
    if (suffix === "ℕ") {
      if (/ \d$/.test(_typewriter)) {
        suffix = ((+_typewriter.slice(-2) + 1) % 10).toString()
        _typewriter = _typewriter.slice(0, -2)
      } else {
        suffix = "0"
      }
      suffix = " " + suffix
    } else if (suffix === "∈" && _typewriter.endsWith("∈")) {
      suffix = " {} "
    } else if (isAssumption && /^apply |^symm|^push_neg/.test(_typewriter)) {
      suffix = " at " + suffix
    } else if (suffix === "have") {
      suffix = _typewriter === "have :" ? "=" : " :="
    } else if (/[\]}]$/.test(_typewriter)) {
      if (isAssumption) {
        suffix = " at " + suffix
      } else {
        const closing = _typewriter.slice(-1)
        _typewriter = _typewriter.slice(0, -1)
        if (suffix === "←") {
          const imbalance = (_typewriter.match(/\(/)?.length ?? 0) - (_typewriter.match(/\)/)?.length ?? 0)
          suffix = /[[,({]$/.test(_typewriter) ? "←" : /\([^)]*$/.test(_typewriter) ? ")" : " ("
        } else {
          if (!/[[,({]$/.test(_typewriter)) {
            suffix = (isTheorem && !_typewriter.endsWith("←") && closing === "]" ? ", " : /^[ᶜ.]/.test(suffix) ? "" : " ") + suffix
          }
        }
        suffix = suffix + closing
      }
    } else if (!/^[ᶜ.]/.test(suffix)) {
      suffix = " " + suffix
    }
    setTypewriter(`${_typewriter}${suffix} `.trimStart())
    return true
  }
}
