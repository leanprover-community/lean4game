/**
 *  @fileOverview This file contains the the react contexts used in the project.
 */
import * as React from 'react';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { InteractiveDiagnostic, InteractiveTermGoal } from '@leanprover/infoview-api';
import { InteractiveGoal, InteractiveGoals } from './rpc_api';

export const MonacoEditorContext = React.createContext<monaco.editor.IStandaloneCodeEditor>(
  null as any)

export type InfoStatus = 'updating' | 'error' | 'ready';

/** One step of the proof */
export type ProofStep = {
  /** The command in this step */
  command : string
  /** List of goals *after* this command */
  goals: InteractiveGoal[]     // TODO: Add correct type
  /** Story relevant messages */
  hints: any        // TODO: Add correct type
  /** Errors and warnings */
  errors: InteractiveDiagnostic[]       // TODO: Add correct type
}

/** The context storing the proof step-by-step for the command line mode */
export const ProofContext = React.createContext<{
  /** The proof consists of multiple steps that are processed one after the other.
   * In particular multi-line terms like `match`-statements will not be supported.
   *
   * Note that the first step will always have `null` as command
   */
  proof: ProofStep[],
  setProof: React.Dispatch<React.SetStateAction<Array<ProofStep>>>
}>({
  proof: [],
  setProof: () => {} // TODO: implement me
})

// TODO: Is this still used?
export const HintContext = React.createContext<{
  showHiddenHints : boolean,
  setShowHiddenHints: React.Dispatch<React.SetStateAction<boolean>>
}>({
  showHiddenHints: true,
  setShowHiddenHints: () => {},
});

export interface ProofStateProps {
  // pos: DocumentPosition;
  status: InfoStatus;
  messages: InteractiveDiagnostic[];
  goals?: InteractiveGoals;
  termGoal?: InteractiveTermGoal;
  error?: string;
  // userWidgets: UserWidgetInstance[];
  // rpcSess: RpcSessionAtPos;
  // triggerUpdate: () => Promise<void>;
}

export const ProofStateContext = React.createContext<{
  proofState : ProofStateProps,
  setProofState: React.Dispatch<React.SetStateAction<ProofStateProps>>
}>({
  proofState : {
    status: 'updating',
    messages: [],
    goals: undefined,
    termGoal: undefined,
    error: undefined},
  setProofState: () => {},
});

export const InputModeContext = React.createContext<{
  commandLineMode: boolean,
  setCommandLineMode: React.Dispatch<React.SetStateAction<boolean>>,
  commandLineInput: string,
  setCommandLineInput: React.Dispatch<React.SetStateAction<string>>
}>({
  commandLineMode: true,
  setCommandLineMode: () => {},
  commandLineInput: "",
  setCommandLineInput: () => {},
});
