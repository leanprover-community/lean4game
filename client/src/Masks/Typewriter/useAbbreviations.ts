import {
  type AbbreviationConfig,
  AbbreviationProvider,
  AbbreviationRewriter,
  type AbbreviationTextSource,
  type Change,
  Range,
  type SelectionMoveMode,
} from '@leanprover/unicode-input'
import { type RefObject, useLayoutEffect, useState } from 'react'

const config: AbbreviationConfig = {
  abbreviationCharacter: '\\',
  customTranslations: {},
  eagerReplacementEnabled: true,
}
const provider = new AbbreviationProvider(config)

/**
 * The first `count` distinct symbols for the abbreviation being typed, with their full
 * abbreviations. They are in the provider's order, so the first one is what the
 * abbreviation would be replaced with. A symbol may contain `$CURSOR`.
 */
export function abbreviationSuggestions(typed: string, count: number) {
  const symbols = provider.getSymbolsByAbbreviation()
  const abbreviations = Object.keys(symbols)
    .filter(abbreviation => abbreviation.startsWith(typed))
    .toSorted((a, b) => a.length - b.length)
  const bySymbol = new Map<string, string>()
  for (const abbreviation of abbreviations) {
    const symbol = symbols[abbreviation]
    if (!bySymbol.has(symbol)) bySymbol.set(symbol, abbreviation)
    if (bySymbol.size === count) break
  }
  return [...bySymbol].map(([symbol, abbreviation]) => ({
    symbol,
    abbreviation,
  }))
}

/**
 * The change from `before` to `after`, with the cursor at `cursor` afterwards. The text
 * behind the cursor is taken as unchanged where possible, which tells where a character
 * was inserted among equal ones.
 */
function diff(before: string, after: string, cursor: number): Change {
  const maxEnd = Math.min(before.length, after.length - cursor)
  let end = 0
  while (end < maxEnd && before.at(-1 - end) === after.at(-1 - end)) end++
  const maxStart = Math.min(before.length, after.length) - end
  let start = 0
  while (start < maxStart && before[start] === after[start]) start++
  return {
    range: new Range(start, before.length - end - start),
    newText: after.slice(start, after.length - end),
  }
}

/** Connects a textarea to the `AbbreviationRewriter` of `@leanprover/unicode-input` */
class TextareaAbbreviations implements AbbreviationTextSource {
  private readonly rewriter = new AbbreviationRewriter(config, provider, this)
  /** the text the rewriter knows about */
  private text = ''
  private composing = false
  private onChange: (value: string) => void = () => {}
  private readonly textarea: RefObject<HTMLTextAreaElement | null>
  private readonly listeners = new Set<() => void>()

  constructor(textarea: RefObject<HTMLTextAreaElement | null>) {
    this.textarea = textarea
  }

  /** To be called after each render with the current props of the input */
  update(value: string, onChange: (value: string) => void) {
    this.onChange = onChange
    // the text was set from outside: the positions of the abbreviations are void
    if (value === this.text) return
    this.text = value
    this.rewriter.resetTrackedAbbreviations()
    this.notify()
  }

  /** For `useSyncExternalStore`, to follow `typed` */
  subscribe = (listener: () => void) => {
    this.listeners.add(listener)
    return () => {
      this.listeners.delete(listener)
    }
  }

  private notify() {
    for (const listener of this.listeners) listener()
  }

  /** The abbreviation being typed, without the backslash, `undefined` if there is none */
  typed = () => this.current()?.abbreviation

  /** A finished abbreviation only waits for an input method to end to be replaced */
  private current() {
    return [...this.rewriter.getTrackedAbbreviations()].find(a => !a.finished)
  }

  /** Completes the abbreviation being typed to `abbreviation` and replaces it */
  async accept(abbreviation: string) {
    const textarea = this.textarea.current
    const current = this.current()
    if (!textarea || !current) return
    const end = current.range.offset + current.range.length
    textarea.setRangeText(
      abbreviation.slice(current.abbreviation.length),
      end,
      end,
      'end',
    )
    this.input()
    await this.replaceAll()
    textarea.focus()
  }

  /** To be called after each change of the text by the player */
  input() {
    const textarea = this.textarea.current
    if (!textarea) return
    if (textarea.value !== this.text) {
      const change = diff(this.text, textarea.value, textarea.selectionEnd)
      this.text = textarea.value
      this.rewriter.changeInput([change])
      this.onChange(textarea.value)
    }
    // changing the text would interrupt an input method, e.g. of a mobile keyboard
    if (!this.composing) void this.rewriter.triggerAbbreviationReplacement()
    this.notify()
  }

  /** To be called when the selection changed: leaving an abbreviation replaces it */
  select() {
    // a change of the text which we are about to be told, not a move of the cursor
    const textarea = this.textarea.current
    if (!textarea || this.composing || textarea.value !== this.text) return
    void this.rewriter.changeSelections(this.collectSelections())
    this.notify()
  }

  compositionStart() {
    this.composing = true
  }

  compositionEnd() {
    this.composing = false
    this.input()
  }

  /** Whether an abbreviation is being typed, which `replaceAll` would replace */
  get tracking() {
    return this.rewriter.getTrackedAbbreviations().size > 0
  }

  /** Replaces the abbreviations being typed and returns the resulting text */
  async replaceAll() {
    await this.rewriter.replaceAllTrackedAbbreviations()
    this.notify()
    return this.text
  }

  replaceAbbreviations(changes: Change[]) {
    const textarea = this.textarea.current
    if (!textarea) return Promise.resolve(false)
    // from the end, so that the offsets of the other changes stay valid
    const fromEnd = changes.toSorted((a, b) => b.range.offset - a.range.offset)
    for (const { range, newText } of fromEnd)
      textarea.setRangeText(
        newText,
        range.offset,
        range.offset + range.length,
        'preserve',
      )
    this.text = textarea.value
    // setting the text fires no `input`, but other abbreviations may have to move
    this.rewriter.changeInput(changes)
    this.onChange(textarea.value)
    return Promise.resolve(true)
  }

  selectionMoveMode(): SelectionMoveMode {
    return { kind: 'MoveAllSelections' }
  }

  collectSelections() {
    const textarea = this.textarea.current
    if (!textarea) return []
    const { selectionStart: start, selectionEnd: end } = textarea
    return [new Range(start, end - start)]
  }

  setSelections(selections: Range[]) {
    const selection = selections.at(0)
    if (!selection) return
    this.textarea.current?.setSelectionRange(
      selection.offset,
      selection.offset + selection.length,
    )
  }
}

/**
 * Replaces abbreviations with the unicode symbols of Lean while typing in the textarea
 * `ref`, e.g. `\to` with `→`. This happens as soon as the abbreviation is unambiguous and
 * complete, when it is continued with another character such as a space, when the cursor
 * leaves it, and with `replaceAll`.
 */
export function useAbbreviations(
  ref: RefObject<HTMLTextAreaElement | null>,
  value: string,
  onChange: (value: string) => void,
) {
  const [abbreviations] = useState(() => new TextareaAbbreviations(ref))
  useLayoutEffect(() => abbreviations.update(value, onChange))
  return abbreviations
}
