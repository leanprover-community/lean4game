import { useAtom, useAtomValue } from 'jotai'
import { type FocusEvent, type RefObject, useEffect } from 'react'
import { twMerge } from 'tailwind-merge'

import { selectedStepAtom } from '../state/chat-atoms'

/** The attribute marking the elements of a step, i.e. a proof step and its hints */
const STEP_ATTRIBUTE = 'data-step'

/**
 * Makes an element of the proof step `step` focusable: spread `props` on it and merge
 * `className` into its classes. While focus is inside it, the step is selected, which
 * highlights the step and its hints. Focus moving elsewhere, e.g. into the input line,
 * clears the selection.
 */
export function useStepSelection(step: number) {
  const [selectedStep, setSelectedStep] = useAtom(selectedStepAtom)
  return {
    props: {
      tabIndex: 0,
      [STEP_ATTRIBUTE]: step,
      onFocus: () => setSelectedStep(step),
      onBlur: (e: FocusEvent) => {
        // moving to another step selects that one in its `onFocus`
        const target = e.relatedTarget
        if (
          !(target instanceof Element) ||
          !target.closest(`[${STEP_ATTRIBUTE}]`)
        )
          setSelectedStep(undefined)
      },
    },
    // the highlight replaces the outline
    className: twMerge(
      'outline-none',
      selectedStep === step && 'ring-2 ring-primary',
    ),
  }
}

/** The closest ancestor of `element` which scrolls vertically */
function scrollParent(element: Element) {
  for (let el = element.parentElement; el; el = el.parentElement) {
    const { overflowY } = getComputedStyle(el)
    if (overflowY === 'auto' || overflowY === 'scroll') return el
  }
  return null
}

/**
 * Scrolls to the start of the first element of the selected step inside `ref`. Unlike
 * `scrollIntoView`, smooth scrolling the chat and the proof at the same time works.
 */
export function useScrollToSelectedStep(ref: RefObject<HTMLElement | null>) {
  const selectedStep = useAtomValue(selectedStepAtom)
  useEffect(() => {
    if (selectedStep === undefined) return
    const element = ref.current?.querySelector(
      `[${STEP_ATTRIBUTE}="${selectedStep}"]`,
    )
    const scroller = element && scrollParent(element)
    if (!scroller) return
    const offset =
      element.getBoundingClientRect().top - scroller.getBoundingClientRect().top
    // leave room for the highlight
    scroller.scrollTo({
      top: scroller.scrollTop + offset - 8,
      behavior: 'smooth',
    })
  }, [ref, selectedStep])
}
