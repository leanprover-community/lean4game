import { InteractiveHypothesisBundle, InteractiveHypothesisBundle_nonAnonymousNames, MVarId, TaggedText_stripTags } from "@leanprover/infoview-api"
import React from "react"
import {useAppendTypewriterInput} from "../useAppendTypewriterInput"

interface HypProps {
    hyp: InteractiveHypothesisBundle
    mvarId?: MVarId
}

function isInaccessibleName(h: string): boolean {
    return h.indexOf('✝') >= 0;
}

export function Hyp({ hyp: h, mvarId }: HypProps) {
    const namecls: string = 'mr1 hyp-name ' +
        (h.isInserted ? 'inserted-text ' : '') +
        (h.isRemoved ? 'removed-text ' : '')

    const appendTypewriterInput = useAppendTypewriterInput()

    const names = InteractiveHypothesisBundle_nonAnonymousNames(h).map((n, i) =>
        <span
            className={namecls + (isInaccessibleName(n) ? 'goal-inaccessible ' : '')}
            key={i}
            // FIXME: 3rd argument looks wrong
            onClick={ev => {
                appendTypewriterInput(ev.shiftKey, n, (h as any).isAssumption ?? false, (h as any).isAssumption ?? false)
                ev.stopPropagation()
            } }
        >{n}
        </span>)
    return <div>
        <strong className="goal-hyp">{names}</strong>
        :&nbsp;
        {TaggedText_stripTags(h.type)}
        {h.val && `&nbsp;:=&nbsp;${h.val}`}
    </div>
}
