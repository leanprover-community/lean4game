import { atom } from "jotai";
import { editor } from 'monaco-editor'

/** The editor powering the typewriter (single line) input */
export const oneLineEditorAtom = atom<editor.IStandaloneCodeEditor | null>(null)
