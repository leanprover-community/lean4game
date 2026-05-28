import { useAtom } from "jotai"
import { typewriterAtom, typewriterContentAtom } from "../../../store/editor-atoms"
import { preferencesAtom } from "../../../store/preferences-atoms"

// FIXME: implement
// Step 1: Copy over from infoview/context
// Step 2: Auto-import the used atoms
// Step 3: Copy SUFFIX and PREFIX OVERRIDES into function scpe
// Step 4: Reformulate parameters to adhere to old implementation
// Step 5: Relocate useAtoms into enclosing scope of function to stop infinite re-renders
export function useAppendTypewriterInput() {
  const [typewriterContent] = useAtom(typewriterContentAtom)
  const [, setTypewriter] = useAtom(typewriterAtom)
  const [{ isSuggestionsMobileMode }] = useAtom(preferencesAtom)

  const SUFFIX_OVERRIDES: Record<string, string> = {
    "induction": "generalizing",
    "left": ".left",
    "rewrite": "←",
    "right": ".right",
    "rw": "←",
  }

        const PREFIX_OVERRIDES: Record<string, string> = {
        "by_cases": "by_cases this :",
        "contrapose": "contrapose!",
        "have": "have :",
        "obtain": "obtain ⟨⟩ :=",
        "rewrite": "rw []",
        "rw": "rw []",
        "simp": "simp only []",
        }

        return (shiftKey: boolean, suffix: string, isTheorem: boolean, isAssumption: boolean) => {
          //return (shiftKey: boolean, suffix: string, isTheorem: boolean, isAssumption: boolean) => {
          if (!isSuggestionsMobileMode && !shiftKey) {
              return false
          }
          // Automagically detect and adjust punctuation for mobile keyboardless usage
          let _typewriter = typewriterContent.trim()

          if (!typewriterContent.length) {
              _typewriter = Object.hasOwn(PREFIX_OVERRIDES, suffix) ? PREFIX_OVERRIDES[suffix] : isTheorem ? `rw [${suffix}]` : suffix
              setTypewriter(_typewriter + " ")
              return true
          }

          suffix = !isAssumption && Object.hasOwn(SUFFIX_OVERRIDES, suffix) ? SUFFIX_OVERRIDES[suffix] : suffix

          if (suffix === "ℕ") {
              if (/ \d$/.test(_typewriter)) {
              suffix = ((+_typewriter.slice(-2) + 1) % 10).toString()
              _typewriter = _typewriter.slice(0, -2)
              } else {
              suffix = "0"
              }
              suffix = " " + suffix
          } else if (suffix === "∈" && _typewriter.endsWith("∈")) {
              suffix = " {} "
          } else if (isAssumption && /^apply |^symm|^push_neg/.test(_typewriter)) {
              suffix = " at " + suffix
          } else if (suffix === "have") {
              suffix = _typewriter === "have :" ? "=" : " :="
          } else if (/[\]}]$/.test(_typewriter)) {
              if (isAssumption) {
              suffix = " at " + suffix
              } else {
              const closing = _typewriter.slice(-1)
              _typewriter = _typewriter.slice(0, -1)
              if (suffix === "←") {
                  const imbalance = (_typewriter.match(/\(/)?.length ?? 0) - (_typewriter.match(/\)/)?.length ?? 0)
                  suffix = /[[,({]$/.test(_typewriter) ? "←" : /\([^)]*$/.test(_typewriter) ? ")" : " ("
              } else {
                  if (!/[[,({]$/.test(_typewriter)) {
                  suffix = (isTheorem && !_typewriter.endsWith("←") && closing === "]" ? ", " : /^[ᶜ.]/.test(suffix) ? "" : " ") + suffix
                  }
              }
              suffix = suffix + closing
              }
          } else if (!/^[ᶜ.]/.test(suffix)) {
              suffix = " " + suffix
          }
          setTypewriter(`${_typewriter}${suffix} `.trimStart())
          return true
      }
    }
