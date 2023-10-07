/**
 *  @fileOverview This file contains the the react contexts used in the project.
 */
import * as React from 'react';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { InteractiveDiagnostic, InteractiveTermGoal } from '@leanprover/infoview-api';
import { GameHint, InteractiveGoal, InteractiveGoals } from './rpc_api';

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
  hints: GameHint[]        // TODO: Add correct type
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
})

export const MobileContext = React.createContext<{
  mobile : boolean,
  setMobile: React.Dispatch<React.SetStateAction<Boolean>>,
  pageNumber: number,
  setPageNumber: React.Dispatch<React.SetStateAction<Number>>
}>({
  mobile : false,
  setMobile: () => {},
  pageNumber: 0,
  setPageNumber: () => {}
})

export const WorldLevelIdContext = React.createContext<{
  worldId : string,
  levelId: number
}>({
  worldId : null,
  levelId: 0,
})

/** Context to keep highlight selected proof step and corresponding chat messages. */
export const SelectionContext = React.createContext<{
  selectedStep : number,
  setSelectedStep: React.Dispatch<React.SetStateAction<number>>
}>({
  selectedStep : undefined,
  setSelectedStep: () => {}
})

/** Context for deleted Hints that are visible just a bit after they've been deleted */
export const DeletedChatContext = React.createContext<{
  deletedChat : GameHint[],
  setDeletedChat: React.Dispatch<React.SetStateAction<Array<GameHint>>>
  showHelp : Set<number>,
  setShowHelp: React.Dispatch<React.SetStateAction<Set<number>>>
}>({
  deletedChat: undefined,
  setDeletedChat: () => {},
  showHelp: undefined,
  setShowHelp: () => {}
})

export const InputModeContext = React.createContext<{
  typewriterMode: boolean,
  setTypewriterMode: React.Dispatch<React.SetStateAction<boolean>>,
  typewriterInput: string,
  setTypewriterInput: React.Dispatch<React.SetStateAction<string>>
}>({
  typewriterMode: true,
  setTypewriterMode: () => {},
  typewriterInput: "",
  setTypewriterInput: () => {},
});
