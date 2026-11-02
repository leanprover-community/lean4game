import { useAtom, useAtomValue } from 'jotai'

import type { ApiHint } from '../api'
import { helpAtom } from '../state/chat-atoms'
import { hasError, proofCheckAtom } from '../state/proof-atoms'

/** The hints without the hidden ones, apart from the first `revealed` of them */
function revealedHints(hints: ApiHint[], revealed: number) {
  let n = 0
  return hints.filter(hint => !hint.hidden || n++ < revealed)
}

/** Drops hints already shown in the previous step. Hidden hints are not filtered. */
function filterHints(hints: ApiHint[], prevHints: ApiHint[] | undefined) {
  if (!prevHints) return hints
  return hints.filter(
    hint =>
      hint.hidden ||
      !prevHints.some(x => x.text === hint.text && x.hidden === hint.hidden),
  )
}

/**
 * The hints of the current proof, shown in the chat and on mobile in the proof itself.
 * `hints` are the ones to show by proof step. Hidden hints are revealed one by one with
 * `revealNextHint` at the `current` step, as long as `hiddenLeft`. `completed` is
 * whether the current proof is complete without warnings, i.e. one can go on.
 */
export function useLevelHints() {
  const check = useAtomValue(proofCheckAtom)
  const [help, revealHint] = useAtom(helpAtom)
  const steps = check.data?.steps ?? []
  // a failed last step has the same hints as the step before
  const shown =
    steps.length > 1 && hasError(steps.at(-1)) ? steps.slice(0, -1) : steps
  const current = shown.length - 1
  const revealed = help.get(current) ?? 0
  return {
    hints: shown.map((step, i) =>
      filterHints(
        revealedHints(step.goals[0]?.hints ?? [], help.get(i) ?? 0),
        shown[i - 1]?.goals[0]?.hints,
      ),
    ),
    current,
    hiddenLeft:
      (shown[current]?.goals[0]?.hints.filter(hint => hint.hidden).length ??
        0) > revealed,
    revealNextHint: () => revealHint(current),
    // not while the previous result is shown during a new check
    completed: !check.isPlaceholderData && (check.data?.completed ?? false),
    /** changes when a message is added at the end */
    newestKey: `${shown.length}:${revealed}`,
  }
}
