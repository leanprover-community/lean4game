import type { LeanInstance } from './leanInstances.js'

/*
This file provides basic functionality to open, modify, and close a file in the Lean server.
It implements a queue which ensures that every instance only has one active check and at
most one in queue any further request replaces the queued one.
*/

/** A queued check was replaced by a newer one before it started. */
export class CheckSupersededError extends Error {
  constructor() {
    super('Superseded by a newer check')
  }
}

/** A check took longer than `CHECK_TIMEOUT_MS`. */
export class CheckTimeoutError extends Error {
  constructor() {
    super('Proof check timed out')
  }
}

const CHECK_TIMEOUT_MS = Number(process.env.LEAN_CHECK_TIMEOUT_MS) || 120_000

interface QueuedCheck {
  task: () => Promise<unknown>
  onTimeout: () => void
  resolve: (value: any) => void
  reject: (reason: unknown) => void
}

interface CheckSlot {
  running: boolean
  queued?: QueuedCheck
}

const slots = new Map<string, CheckSlot>()

/**
 * Runs `task` once the running check of the instance is done. A check which is
 * still waiting is replaced and rejected with `CheckSupersededError`.
 *
 * A running check is rejected with `CheckTimeoutError` after `CHECK_TIMEOUT_MS`,
 * after calling `onTimeout`. The next check starts right away, even if the
 * Lean server is still working on the old one.
 */
export function scheduleCheck<T>(
  instanceId: string,
  task: () => Promise<T>,
  onTimeout: () => void,
): Promise<T> {
  let slot = slots.get(instanceId)
  if (!slot) {
    slot = { running: false }
    slots.set(instanceId, slot)
  }
  return new Promise<T>((resolve, reject) => {
    const check = { task, onTimeout, resolve, reject }
    if (!slot.running) {
      runCheck(slot, check)
      return
    }
    slot.queued?.reject(new CheckSupersededError())
    slot.queued = check
  })
}

function runCheck(slot: CheckSlot, check: QueuedCheck): void {
  slot.running = true
  let timer: NodeJS.Timeout | undefined
  const timeout = new Promise<never>((_, reject) => {
    timer = setTimeout(() => {
      check.onTimeout()
      reject(new CheckTimeoutError())
    }, CHECK_TIMEOUT_MS)
  })
  Promise.race([check.task(), timeout])
    .then(check.resolve, check.reject)
    .finally(() => {
      clearTimeout(timer)
      const next = slot.queued
      slot.queued = undefined
      if (next) runCheck(slot, next)
      else slot.running = false
    })
}

/** A document kept open in the Lean server */
export interface OpenDoc {
  uri: string
  version: number
  text: string
}

const MAX_OPEN_DOCS = Math.max(1, Number(process.env.LEAN_MAX_OPEN_DOCS) || 1)

/** All currently open documents.
 * Inside the map, the most recently used document always comes last
 */
const openDocs = new Map<string, Map<string, OpenDoc>>()

/** Forgets the open documents of an instance whose process has exited */
export function forgetInstanceDocs(instanceId: string): void {
  openDocs.delete(instanceId)
  slots.get(instanceId)?.queued?.reject(new Error('Lean server exited'))
  slots.delete(instanceId)
}

/**
 * Close a document. If `expected` is given, only if it is still that document,
 * so that a check which timed out can't close the document of a newer check.
 */
export async function closeDoc(
  instance: LeanInstance,
  uri: string,
  expected?: OpenDoc,
): Promise<void> {
  const docs = openDocs.get(instance.id)
  if (!docs) return
  if (expected && docs.get(uri) !== expected) return
  docs.delete(uri)
  await instance.client
    .notify('textDocument/didClose', { textDocument: { uri } })
    .catch(() => {})
}

/** Opens a new document or updates its content if already open */
export async function syncDoc(
  instance: LeanInstance,
  uri: string,
  text: string,
): Promise<OpenDoc> {
  let docs = openDocs.get(instance.id)
  if (!docs) {
    docs = new Map()
    openDocs.set(instance.id, docs)
  }
  let doc = docs.get(uri)
  if (!doc) {
    doc = { uri, version: 1, text }
    await instance.client.notify('textDocument/didOpen', {
      textDocument: { uri, languageId: 'lean4', version: doc.version, text },
      // never let a check build the game or its dependencies. Imported games must come fully built.
      dependencyBuildMode: 'never',
    })
  } else if (doc.text !== text) {
    doc.version++
    doc.text = text
    await instance.client.notify('textDocument/didChange', {
      textDocument: { uri, version: doc.version },
      contentChanges: [{ text }],
    })
  }
  // move file to the end and delete files which haven't been used the longest
  docs.delete(uri)
  docs.set(uri, doc)
  for (const oldUri of docs.keys()) {
    if (docs.size <= MAX_OPEN_DOCS) break
    await closeDoc(instance, oldUri)
  }
  return doc
}
