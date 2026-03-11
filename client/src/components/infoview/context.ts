/**
 *  @fileOverview This file contains the the react contexts used in the project.
 */
import * as React from 'react';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { InteractiveDiagnostic } from '@leanprover/infoview-api';
import { Diagnostic } from 'vscode-languageserver-types'
import { GameHint, InteractiveGoal, InteractiveTermGoal,InteractiveGoalsWithHints, ProofState } from './rpc_api';
import { Preferences, preferencesAtom } from '../../store/preferences-atoms';
import { useAtom } from 'jotai';

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

/** The context storing the proof step-by-step for the command line mode */
export const ProofContext = React.createContext<{
  /** The proof consists of multiple steps that are processed one after the other.
   * In particular multi-line terms like `match`-statements will not be supported.
   *
   * Note that the first step will always have "" as command
   */
  proof: ProofState,
  setProof: React.Dispatch<React.SetStateAction<ProofState>>
  /** TODO: Workaround to capture a crash of the gameserver. */
  interimDiags: Diagnostic[],
  setInterimDiags: React.Dispatch<React.SetStateAction<Array<Diagnostic>>>
  /** TODO: Workaround to capture a crash of the gameserver. */
  crashed: boolean,
  setCrashed: React.Dispatch<React.SetStateAction<Boolean>>
}>({
  proof: {steps: [], diagnostics: [], completed: false, completedWithWarnings: false},
  setProof: () => {},
  interimDiags: [],
  setInterimDiags: () => {},
  crashed: false,
  setCrashed: () => {}
})


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
  setIsSuggestionsMobileMode: any;
}

/** Context to keep highlight selected proof step and corresponding chat messages. */
export const SelectionContext = React.createContext<{
  selectedStep : number | null,
  setSelectedStep: React.Dispatch<React.SetStateAction<number | null>>
}>({
  selectedStep : null,
  setSelectedStep: () => {}
})

/** Context for deleted Hints that are visible just a bit after they've been deleted */
export const DeletedChatContext = React.createContext<{
  deletedChat : GameHint[],
  setDeletedChat: React.Dispatch<React.SetStateAction<Array<GameHint>>>
  showHelp : Set<number>,
  setShowHelp: React.Dispatch<React.SetStateAction<Set<number>>>
}>({
  deletedChat: [],
  setDeletedChat: () => {},
  showHelp: new Set(),
  setShowHelp: () => {}
})

export const InputModeContext = React.createContext<{
  typewriterInput: string,
  setTypewriterInput: React.Dispatch<React.SetStateAction<string>>,
  lockEditorMode: boolean,
  setLockEditorMode: React.Dispatch<React.SetStateAction<boolean>>,
}>({
  typewriterInput: "",
  setTypewriterInput: () => {},
  lockEditorMode: false,
  setLockEditorMode: () => {},
});


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
  let {typewriterInput, setTypewriterInput} = React.useContext(InputModeContext)
  const [{ isSuggestionsMobileMode }] = useAtom(preferencesAtom)
  return (shiftKey: boolean, suffix: string, isTheorem: boolean, isAssumption: boolean) => {
    if (!isSuggestionsMobileMode && !shiftKey) {
      return false
    }
    // Automagically detect and adjust punctuation for mobile keyboardless usage
    typewriterInput = typewriterInput.trim()
    if (!typewriterInput.length) {
      typewriterInput = Object.hasOwn(PREFIX_OVERRIDES, suffix) ? PREFIX_OVERRIDES[suffix] : isTheorem ? `rw [${suffix}]` : suffix
      setTypewriterInput(typewriterInput + " ")
      return true
    }
    suffix = !isAssumption && Object.hasOwn(SUFFIX_OVERRIDES, suffix) ? SUFFIX_OVERRIDES[suffix] : suffix
    if (suffix === "ℕ") {
      if (/ \d$/.test(typewriterInput)) {
        suffix = ((+typewriterInput.slice(-2) + 1) % 10).toString()
        typewriterInput = typewriterInput.slice(0, -2)
      } else {
        suffix = "0"
      }
      suffix = " " + suffix
    } else if (suffix === "∈" && typewriterInput.endsWith("∈")) {
      suffix = " {} "
    } else if (isAssumption && /^apply |^symm|^push_neg/.test(typewriterInput)) {
      suffix = " at " + suffix
    } else if (suffix === "have") {
      suffix = typewriterInput === "have :" ? "=" : " :="
    } else if (/[\]}]$/.test(typewriterInput)) {
      if (isAssumption) {
        suffix = " at " + suffix
      } else {
        const closing = typewriterInput.slice(-1)
        typewriterInput = typewriterInput.slice(0, -1)
        if (suffix === "←") {
          const imbalance = (typewriterInput.match(/\(/)?.length ?? 0) - (typewriterInput.match(/\)/)?.length ?? 0)
          suffix = /[[,({]$/.test(typewriterInput) ? "←" : /\([^)]*$/.test(typewriterInput) ? ")" : " ("
        } else {
          if (!/[[,({]$/.test(typewriterInput)) {
            suffix = (isTheorem && !typewriterInput.endsWith("←") && closing === "]" ? ", " : /^[ᶜ.]/.test(suffix) ? "" : " ") + suffix
          }
        }
        suffix = suffix + closing
      }
    } else if (!/^[ᶜ.]/.test(suffix)) {
      suffix = " " + suffix
    }
    setTypewriterInput(`${typewriterInput}${suffix} `.trimLeft())
    return true
  }
}
