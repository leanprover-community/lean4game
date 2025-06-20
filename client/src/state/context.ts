/**
 *  @fileOverview This file contains the the react contexts used in the project.
 */
import * as React from 'react';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { InteractiveDiagnostic } from '@leanprover/infoview-api';
import { Diagnostic } from 'vscode-languageserver-types'
import { GameHint, InteractiveGoal, InteractiveTermGoal, InteractiveGoalsWithHints, ProofState } from '../components/editor/Defs';
import { PreferencesState } from './preferences';
import { LeanMonaco, LeanMonacoEditor } from 'lean4monaco';
import { RpcSessionAtPos } from 'lean4monaco/dist/vscode-lean4/vscode-lean4/src/infoview';

export const MonacoEditorContext = React.createContext<{
  leanMonacoEditor: LeanMonacoEditor
  leanMonaco: LeanMonaco
  rpcSess: RpcSessionAtPos
}>(null)

export type InfoStatus = 'updating' | 'error' | 'ready';


export const GameIdContext = React.createContext<{
  gameId: string,
  worldId: string|null,
  levelId: number|null}>({gameId: null, worldId: null, levelId: null});

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
  crashed: Boolean,
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

export interface IPreferencesContext extends PreferencesState{
  mobile: boolean, // The variables that actually control the page 'layout' can only be changed through layout.
  setLayout: React.Dispatch<React.SetStateAction<PreferencesState["layout"]>>;
  setIsSavePreferences: React.Dispatch<React.SetStateAction<PreferencesState["isSavePreferences"]>>;
  setLanguage: React.Dispatch<React.SetStateAction<PreferencesState["language"]>>;
}

export const PreferencesContext = React.createContext<IPreferencesContext>({
  mobile: false,
  layout: "auto",
  isSavePreferences: false,
  language: "en",
  setLayout: () => {},
  setIsSavePreferences: () => {},
  setLanguage: () => {},
})


export const ChatContext = React.createContext<{
  selectedStep : number
  setSelectedStep: React.Dispatch<React.SetStateAction<number>>
  deletedChat : GameHint[]
  setDeletedChat: React.Dispatch<React.SetStateAction<Array<GameHint>>>
  showHelp : Set<number>
  setShowHelp: React.Dispatch<React.SetStateAction<Set<number>>>
  chatRef: React.MutableRefObject<HTMLDivElement>
}>({
  selectedStep : undefined,
  setSelectedStep: () => {},
  deletedChat: undefined,
  setDeletedChat: () => {},
  showHelp: undefined,
  setShowHelp: () => {},
  chatRef: null
})

export const PageContext = React.createContext<{
  typewriterMode: boolean,
  setTypewriterMode: React.Dispatch<React.SetStateAction<boolean>>,
  typewriterInput: string,
  setTypewriterInput: React.Dispatch<React.SetStateAction<string>>,
  lockEditorMode: boolean,
  setLockEditorMode: React.Dispatch<React.SetStateAction<boolean>>,
  page: number, /* only for mobile */
  setPage: React.Dispatch<React.SetStateAction<number>>,
}>({
  typewriterMode: true,
  setTypewriterMode: () => {},
  typewriterInput: "",
  setTypewriterInput: () => {},
  lockEditorMode: false,
  setLockEditorMode: () => {},
  page: 0,
  setPage: () => {}
});

export const InputModeContext = React.createContext<{
  typewriterMode: boolean,
  setTypewriterMode: React.Dispatch<React.SetStateAction<boolean>>,
  typewriterInput: string,
  setTypewriterInput: React.Dispatch<React.SetStateAction<string>>,
  lockEditorMode: boolean,
  setLockEditorMode: React.Dispatch<React.SetStateAction<boolean>>,
}>({
  typewriterMode: true,
  setTypewriterMode: () => {},
  typewriterInput: "",
  setTypewriterInput: () => {},
  lockEditorMode: false,
  setLockEditorMode: () => {},
});
