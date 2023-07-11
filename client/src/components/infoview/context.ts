/**
 *  @fileOverview This file contains the the react contexts used in the project.
 */
import * as React from 'react';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { InteractiveDiagnostic, InteractiveTermGoal } from '@leanprover/infoview-api';
import { InteractiveGoals } from './rpc_api';

export const MonacoEditorContext = React.createContext<monaco.editor.IStandaloneCodeEditor>(
  null as any)

// TODO: Is this still used?
export const HintContext = React.createContext<{
  showHiddenHints : boolean,
  setShowHiddenHints: React.Dispatch<React.SetStateAction<boolean>>
}>({
  showHiddenHints: true,
  setShowHiddenHints: () => {},
});

export type InfoStatus = 'updating' | 'error' | 'ready';

export type ProofStep = {
  // TODO: Add correct types
  command : string
  goals: string
  hints: string
  errors: string
}

export const ProofContext = React.createContext<{
  // The first entry will always have an empty/undefined command
  proof: ProofStep[],
  setProof: React.Dispatch<React.SetStateAction<Array<ProofStep>>>
}>({
  proof: [],
  setProof: () => {}
})

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
