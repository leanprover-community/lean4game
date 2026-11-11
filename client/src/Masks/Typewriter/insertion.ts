/**
 * Inserting tactics, theorems and hypotheses into the typewriter's input line by
 * clicking them. A tactic inserts its template (see `TacticDoc` on the Lean side), whose
 * slots then take the names and tactics clicked afterwards, from left to right. The slots move along
 * when the player edits the text, so typing and clicking can be mixed.
 */

/** What a slot takes and how its items are separated, see `parseTemplate` */
export type SlotKind = 'single' | 'comma' | 'space' | 'tactics'

/**
 * A slot of an inserted template: the range of the input text with its content, which is
 * empty when it is inserted
 */
export interface Slot {
  kind: SlotKind
  start: number
  end: number
}

/** The input text with its slots and the selection, as offsets into the text */
export interface InputState {
  text: string
  slots: Slot[]
  selection: [number, number]
}

const slotKinds: Record<string, SlotKind> = {
  _: 'single',
  ',': 'comma',
  '+': 'space',
  ';': 'tactics',
}

/**
 * The text of a template like `rw [$,]` and its slots: `$_` takes a single name or
 * tactic, `$,` a comma-separated list and `$+` a space-separated one, and `$;` a sequence
 * of tactics separated by `;`, e.g. after `by`. `$$` is a literal `$`, as is a `$` followed
 * by anything else.
 */
export function parseTemplate(template: string) {
  let text = ''
  const slots: Slot[] = []
  for (let i = 0; i < template.length; i++) {
    const char = template[i]
    const next = template[i + 1] ?? ''
    if (char === '$' && next === '$') {
      text += '$'
      i++
    } else if (char === '$' && next in slotKinds) {
      slots.push({
        kind: slotKinds[next],
        start: text.length,
        end: text.length,
      })
      i++
    } else {
      text += char
    }
  }
  return { text, slots }
}

/**
 * The slots after replacing `removed` characters at `at` by `inserted` ones. A slot grows
 * with text typed at its ends, and is dropped when the change goes beyond its ends.
 */
function shiftSlots(
  slots: Slot[],
  at: number,
  removed: number,
  inserted: number,
): Slot[] {
  const editEnd = at + removed
  const delta = inserted - removed
  return slots.flatMap(slot => {
    if (at > slot.end) return [slot]
    if (at < slot.start) {
      if (editEnd > slot.start) return []
      return [{ ...slot, start: slot.start + delta, end: slot.end + delta }]
    }
    if (editEnd > slot.end) return []
    return [{ ...slot, end: slot.end + delta }]
  })
}

/**
 * Takes over the text after the player edited it, moving the slots along. `caret` is the
 * position of the caret after the edit, if known, to tell where e.g. a `]` typed
 * next to another `]` went.
 */
export function editText(
  state: InputState,
  text: string,
  caret?: number,
): InputState {
  const old = state.text
  const maxPrefix = Math.min(old.length, text.length, caret ?? Infinity)
  let prefix = 0
  while (prefix < maxPrefix && old[prefix] === text[prefix]) prefix++
  const maxSuffix = Math.min(
    old.length - prefix,
    text.length - Math.max(prefix, caret ?? 0),
  )
  let suffix = 0
  while (
    suffix < maxSuffix &&
    old[old.length - 1 - suffix] === text[text.length - 1 - suffix]
  )
    suffix++
  const removed = old.length - prefix - suffix
  const inserted = text.length - prefix - suffix
  const end = caret ?? prefix + inserted
  return {
    text,
    slots: shiftSlots(state.slots, prefix, removed, inserted),
    selection: [end, end],
  }
}

/** Whether a space is needed between `before` and `after` to separate two words */
function needsSpace(before: string, after: string) {
  return (
    before.length > 0 &&
    after.length > 0 &&
    !/[\s([{]$/.test(before) &&
    !/^[\s)\]},]/.test(after)
  )
}

/**
 * Replaces the selection by `inserted`, with spaces around it where it would run into
 * the text next to it. Returns the new state and where `inserted` starts and ends.
 */
function insertAtSelection(state: InputState, inserted: string) {
  const [from, to] = state.selection
  const before = state.text.slice(0, from)
  const after = state.text.slice(to)
  const spaceBefore = needsSpace(before, inserted) ? ' ' : ''
  const spaceAfter = needsSpace(inserted, after) ? ' ' : ''
  const piece = spaceBefore + inserted + spaceAfter
  const start = from + spaceBefore.length
  const end = start + inserted.length
  return {
    state: {
      text: before + piece + after,
      slots: shiftSlots(state.slots, from, to - from, piece.length),
      selection: [end, end] as [number, number],
    },
    start,
    end,
  }
}

/**
 * The index of the innermost slot containing the range `from`–`to`. Slots nest when a
 * template is inserted into another one's slot, e.g. `rw [$,]` after `have … := by`, and
 * the inner slots start within the outer one.
 */
function slotAt(slots: Slot[], from: number, to: number) {
  let found = -1
  slots.forEach((slot, i) => {
    if (slot.start > from || to > slot.end) return
    const best = slots[found] as Slot | undefined
    if (
      !best ||
      slot.start > best.start ||
      (slot.start === best.start &&
        slot.end - slot.start < best.end - best.start)
    )
      found = i
  })
  return found
}

/** The separator to append a tactic to `content`, the tactics in a `$;` slot */
function tacticSeparator(content: string) {
  if (content.trim().length === 0) return ''
  if (!content.trimEnd().endsWith(';')) return '; '
  return /\s$/.test(content) ? '' : ' '
}

/**
 * Appends `text` to the tactics in `slot`, see `tacticSeparator`. Returns the new state
 * and where `text` starts and ends, like `insertAtSelection`.
 */
function appendTactic(state: InputState, slot: Slot, text: string) {
  const separator = tacticSeparator(state.text.slice(slot.start, slot.end))
  const piece = separator + text
  const at = slot.end
  const end = at + piece.length
  return {
    state: {
      text: state.text.slice(0, at) + piece + state.text.slice(at),
      slots: shiftSlots(state.slots, at, 0, piece.length),
      selection: [end, end] as [number, number],
    },
    start: at + separator.length,
    end,
  }
}

/**
 * Inserts a tactic's template at the selection, with the caret in its first slot, or
 * after it if it has none. In a single slot, the tactic fills it, and its own slots take
 * over. In a `$;` slot, it is appended to the tactics there.
 */
export function insertTemplate(
  state: InputState,
  template: string,
): InputState {
  const { text, slots } = parseTemplate(template)
  const enclosing = slotAt(state.slots, ...state.selection)
  const outer = state.slots[enclosing] as Slot | undefined
  if (outer?.kind === 'single') {
    state = { ...state, slots: state.slots.filter((_, i) => i !== enclosing) }
  }
  const inserted =
    outer?.kind === 'tactics'
      ? appendTactic(state, outer, text)
      : insertAtSelection(state, text)
  const newSlots = slots.map(slot => ({
    ...slot,
    start: slot.start + inserted.start,
    end: slot.end + inserted.start,
  }))
  const caret = newSlots[0]?.start ?? inserted.end
  return {
    ...inserted.state,
    slots: [...inserted.state.slots, ...newSlots].toSorted(
      (a, b) => a.start - b.start,
    ),
    selection: [caret, caret],
  }
}

/**
 * Inserts the name of a theorem or hypothesis. If the caret is in a slot (the innermost
 * one, see `slotAt`), the name is added at the end of the slot's content, separated as
 * the slot says. A filled single-name slot is done, and the caret moves on to the next
 * slot. Otherwise the name replaces the selection.
 */
export function insertName(state: InputState, name: string): InputState {
  const [from, to] = state.selection
  const index = from === to ? slotAt(state.slots, from, to) : -1
  const slot = state.slots[index] as Slot | undefined
  // a name alone is no tactic, so it goes to the caret as outside of slots
  if (!slot || slot.kind === 'tactics')
    return insertAtSelection(state, name).state

  const content = state.text.slice(slot.start, slot.end)
  let separator = ''
  if (content.trim().length > 0) {
    if (slot.kind === 'comma' && !content.trimEnd().endsWith(','))
      separator = ', '
    else if (!/\s$/.test(content)) separator = ' '
  }
  const piece = separator + name
  const text =
    state.text.slice(0, slot.end) + piece + state.text.slice(slot.end)
  const slots = shiftSlots(state.slots, slot.end, 0, piece.length)
  const end = slot.end + piece.length
  if (slot.kind !== 'single') return { text, slots, selection: [end, end] }

  // the slot is filled, go on to the next one. Inserting at its end drops no slot, so
  // the indices still match.
  const others = slots.filter((_, i) => i !== index)
  const next = others.find(s => s.start >= end)
  const caret = next?.start ?? end
  return { text, slots: others, selection: [caret, caret] }
}

/**
 * The plain text of an insertion, e.g. to show or copy it: a tactic's template without its
 * slots, e.g. `rw []`, or a name
 */
export function insertionText(
  insertion:
    | { kind: 'tactic'; template: string }
    | { kind: 'name'; name: string },
) {
  return insertion.kind === 'tactic'
    ? parseTemplate(insertion.template).text.trim()
    : insertion.name
}
