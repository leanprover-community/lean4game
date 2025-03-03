import * as React from 'react';
import { InteractiveGoal, InteractiveHypothesisBundle } from '../Defs';
import { useTranslation } from 'react-i18next';
import { InteractiveCode, InteractiveHypothesisBundle_nonAnonymousNames, LocationsContext, SubexprInfo, TaggedText } from '@leanprover/infoview';
import { SelectableLocation } from '../../../../../node_modules/lean4-infoview/src/infoview/goalLocation';

/** Returns true if `h` is inaccessible according to Lean's default name rendering. */
function isInaccessibleName(h: string): boolean {
  return h.indexOf('✝') >= 0;
}

interface GoalFilterState {
  /** If true reverse the list of hypotheses, if false present the order received from LSP. */
  reverse: boolean,
  /** If true show hypotheses that have isType=True, otherwise hide them. */
  showType: boolean,
  /** If true show hypotheses that have isInstance=True, otherwise hide them. */
  showInstance: boolean,
  /** If true show hypotheses that contain a dagger in the name, otherwise hide them. */
  showHiddenAssumption: boolean
  /** If true show the bodies of let-values, otherwise hide them. */
  showLetValue: boolean;
}

interface HypProps {
    hyp: InteractiveHypothesisBundle
    mvarId?: any // MVarId
}

// function Hyp({ hyp: h, mvarId }: HypProps) {
//     const locs = React.useContext(LocationsContext)

//     const namecls: string = 'mr1 ' +
//         (h.isInserted ? 'inserted-text ' : '') +
//         (h.isRemoved ? 'removed-text ' : '')

//     const names = InteractiveHypothesisBundle_nonAnonymousNames(h as InteractiveHypothesisBundle).map((n, i) =>
//         <span className={namecls + (isInaccessibleName(n) ? 'goal-inaccessible ' : '')} key={i}>
//             <SelectableLocation
//                 locs={locs}
//                 loc={mvarId && h.fvarIds && h.fvarIds.length > i ?
//                     { mvarId, loc: { hyp: h.fvarIds[i] }} :
//                     undefined
//                 }
//                 alwaysHighlight={false}
//             >{n}</SelectableLocation>
//         </span>)

//     const typeLocs: Locations | undefined = React.useMemo(() =>
//         locs && mvarId && h.fvarIds && h.fvarIds.length > 0 ?
//             { ...locs, subexprTemplate: { mvarId, loc: { hypType: [h.fvarIds[0], ''] }}} :
//             undefined,
//         [locs, mvarId, h.fvarIds])

//     const valLocs: Locations | undefined = React.useMemo(() =>
//         h.val && locs && mvarId && h.fvarIds && h.fvarIds.length > 0 ?
//             { ...locs, subexprTemplate: { mvarId, loc: { hypValue: [h.fvarIds[0], ''] }}} :
//             undefined,
//         [h.val, locs, mvarId, h.fvarIds])

//     return <div>
//         <strong className="goal-hyp">{names}</strong>
//         :&nbsp;
//         <LocationsContext.Provider value={typeLocs}>
//             <InteractiveCode fmt={h.type} />
//         </LocationsContext.Provider>
//         {h.val &&
//             <LocationsContext.Provider value={valLocs}>
//                 &nbsp;:=&nbsp;<InteractiveCode fmt={h.val} />
//             </LocationsContext.Provider>}
//     </div>
// }

function getFilteredHypotheses(hyps: InteractiveHypothesisBundle[], filter: GoalFilterState): InteractiveHypothesisBundle[] {
    return hyps.reduce((acc: InteractiveHypothesisBundle[], h) => {
        if (h.isInstance && !filter.showInstance) return acc
        if (h.isType && !filter.showType) return acc
        const names = filter.showHiddenAssumption ? h.names : h.names.filter(n => !isInaccessibleName(n))
        const hNew: InteractiveHypothesisBundle = filter.showLetValue ? { ...h, names } : { ...h, names, val: undefined }
        if (names.length !== 0) acc.push(hNew)
        return acc
    }, [])
}

interface GoalProps {
    goal: InteractiveGoal
    filter: GoalFilterState
    showHints?: boolean
    typewriter: boolean
    unbundle?: boolean /** unbundle `x y : Nat` into `x : Nat` and `y : Nat` */
}

/**
 * Displays the hypotheses, target type and optional case label of a goal according to the
 * provided `filter`. */
export const Goal = React.memo((props: GoalProps) => {
    const { goal, filter, showHints, typewriter, unbundle } = props
    let { t } = useTranslation()

    // TODO: Apparently `goal` can be `undefined`
    if (!goal) {return <></>}

    const filteredList = getFilteredHypotheses(goal.hyps, filter);
    const hyps = filter.reverse ? filteredList.slice().reverse() : filteredList;
    const locs = React.useContext(LocationsContext)
    const goalLocs = React.useMemo(() =>
        locs && goal.mvarId ?
            { ...locs, subexprTemplate: { mvarId: goal.mvarId, loc: { target: '' }}} :
            undefined,
        [locs, goal.mvarId])
    const goalLi = <div key={'goal'} className="goal">
        {/* <div className="goal-title">{t("Goal")}:</div> */}
        <LocationsContext.Provider value={goalLocs}>
            <InteractiveCode fmt={goal.type as TaggedText<SubexprInfo>} />
        </LocationsContext.Provider>
    </div>

    // let cn = 'font-code tl pre-wrap bl bw1 pl1 b--transparent '
    // if (props.goal.isInserted) cn += 'b--inserted '
    // if (props.goal.isRemoved) cn += 'b--removed '

    function unbundleHyps (hyps: InteractiveHypothesisBundle[]) : InteractiveHypothesisBundle[] {
        return hyps.flatMap(hyp => (
            unbundle ? hyp.names.map(name => {return {...hyp, names: [name]}}) : [hyp]
        ))
    }

    // const hints = <Hints hints={goal.hints} key={goal.mvarId} />
    const objectHyps = unbundleHyps(hyps.filter(hyp => !hyp.isAssumption))
    const assumptionHyps = unbundleHyps(hyps.filter(hyp => hyp.isAssumption))

    return <>
        {/* {goal.userName && <div><strong className="goal-case">case </strong>{goal.userName}</div>} */}
        {filter.reverse && goalLi}
        <div className="hypotheses">
        {! typewriter && objectHyps.length > 0 &&
            <div className="hyp-group"><div className="hyp-group-title">{t("Objects")}:</div>
            {objectHyps.map((h, i) => <Hyp hyp={h} mvarId={goal.mvarId} key={i} />)}</div> }
        {!typewriter && assumptionHyps.length > 0 &&
            <div className="hyp-group"><div className="hyp-group-title">{t("Assumptions")}:</div>
            {assumptionHyps.map((h, i) => <Hyp hyp={h} mvarId={goal.mvarId} key={i} />)}</div> }
        </div>
        {!filter.reverse && <>
            <div className='goal-sign'>
                <svg width="100%" height="100%">
                    <line x1="0%" y1="0%" x2="0%" y2="100%" />
                    <line x1="0%" y1="50%" x2="100%" y2="50%" />
                </svg>
            </div>
            {goalLi}
        </>}
        {/* {showHints && hints} */}
    </>
})
