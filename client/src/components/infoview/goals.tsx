/**
 * @fileOverview
 *
 * Mostly copied from https://github.com/leanprover/vscode-lean4/blob/master/lean4-infoview/src/infoview/goals.tsx
 */
import * as React from 'react'
// import { InteractiveHypothesisBundle_nonAnonymousNames, MVarId, TaggedText_stripTags } from '@leanprover/infoview-api'
// import { EditorContext } from '../../../../node_modules/lean4-infoview/src/infoview/contexts';
// import { Locations, LocationsContext, SelectableLocation } from '../../../../node_modules/lean4-infoview/src/infoview/goalLocation';
// import { InteractiveCode } from '../../../../node_modules/lean4-infoview/src/infoview/interactiveCode'
// import { WithTooltipOnHover } from '../../../../node_modules/lean4-infoview/src/infoview/tooltips';
import { PageContext } from '../../state/context';
import { InteractiveGoal, InteractiveGoals, InteractiveGoalsWithHints, InteractiveHypothesisBundle, ProofState } from './rpc_api';
// import { RpcSessionAtPos } from '@leanprover/infoview/*';
// import { DocumentPosition } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import { DiagnosticSeverity } from 'vscode-languageserver-protocol';
import { useTranslation } from 'react-i18next';

/** Returns true if `h` is inaccessible according to Lean's default name rendering. */
function isInaccessibleName(h: string): boolean {
    return h.indexOf('✝') >= 0;
}

function goalToString(g: InteractiveGoal): string {
    let ret = ''

    if (g.userName) {
        ret += `case ${g.userName}\n`
    }

    for (const h of g.hyps) {
        const names = InteractiveHypothesisBundle_nonAnonymousNames(h).join(' ')
        ret += `${names} : ${TaggedText_stripTags(h.type)}`
        if (h.val) {
            ret += ` := ${TaggedText_stripTags(h.val)}`
        }
        ret += '\n'
    }

    ret += `⊢ ${TaggedText_stripTags(g.type)}`

    return ret
}

export function goalsToString(goals: InteractiveGoals): string {
    return goals.goals.map(g => goalToString(g)).join('\n\n')
}

export function goalsWithHintsToString(goals: InteractiveGoalsWithHints): string {
    return goals.goals.map(g => goalToString(g.goal)).join('\n\n')
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

interface HypProps {
    hyp: InteractiveHypothesisBundle
    mvarId?: any // MVarId
}

function Hyp({ hyp: h, mvarId }: HypProps) {
    const locs = React.useContext(LocationsContext)

    const namecls: string = 'mr1 ' +
        (h.isInserted ? 'inserted-text ' : '') +
        (h.isRemoved ? 'removed-text ' : '')

    const names = InteractiveHypothesisBundle_nonAnonymousNames(h).map((n, i) =>
        <span className={namecls + (isInaccessibleName(n) ? 'goal-inaccessible ' : '')} key={i}>
            <SelectableLocation
                locs={locs}
                loc={mvarId && h.fvarIds && h.fvarIds.length > i ?
                    { mvarId, loc: { hyp: h.fvarIds[i] }} :
                    undefined
                }
                alwaysHighlight={false}
            >{n}</SelectableLocation>
        </span>)

    const typeLocs: Locations | undefined = React.useMemo(() =>
        locs && mvarId && h.fvarIds && h.fvarIds.length > 0 ?
            { ...locs, subexprTemplate: { mvarId, loc: { hypType: [h.fvarIds[0], ''] }}} :
            undefined,
        [locs, mvarId, h.fvarIds])

    const valLocs: Locations | undefined = React.useMemo(() =>
        h.val && locs && mvarId && h.fvarIds && h.fvarIds.length > 0 ?
            { ...locs, subexprTemplate: { mvarId, loc: { hypValue: [h.fvarIds[0], ''] }}} :
            undefined,
        [h.val, locs, mvarId, h.fvarIds])

    return <div>
        <strong className="goal-hyp">{names}</strong>
        :&nbsp;
        <LocationsContext.Provider value={typeLocs}>
            <InteractiveCode fmt={h.type} />
        </LocationsContext.Provider>
        {h.val &&
            <LocationsContext.Provider value={valLocs}>
                &nbsp;:=&nbsp;<InteractiveCode fmt={h.val} />
            </LocationsContext.Provider>}
    </div>
}

interface GoalProps2 {
  goals: InteractiveGoal[]
  filter: GoalFilterState
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
            <InteractiveCode fmt={goal.type} />
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

export const MainAssumptions = React.memo((props: GoalProps2) => {
  let { t } = useTranslation()
  const { goals, filter } = props

  const goal = goals[0]
  const filteredList = getFilteredHypotheses(goal.hyps, filter);
  const hyps = filter.reverse ? filteredList.slice().reverse() : filteredList;
  const locs = React.useContext(LocationsContext)

  const goalLocs = React.useMemo(() =>
    locs && goal.mvarId ?
      { ...locs, subexprTemplate: { mvarId: goal.mvarId, loc: { target: '' }}} :
        undefined,
      [locs, goal.mvarId])

  const goalLi = <div key={'goal'}>
    <div className="goal-title">{t("Goal") + ":"}</div>
    <LocationsContext.Provider value={goalLocs}>
      <InteractiveCode fmt={goal.type} />
    </LocationsContext.Provider>
  </div>

  const objectHyps = hyps.filter(hyp => !hyp.isAssumption)
  const assumptionHyps = hyps.filter(hyp => hyp.isAssumption)

  return <div id="main-assumptions">
    <div className="goals-section-title">{t("Current Goal")}</div>
    {filter.reverse && goalLi}
    { objectHyps.length > 0 &&
      <div className="hyp-group"><div className="hyp-group-title">{t("Objects") + ":"}</div>
      {objectHyps.map((h, i) => <Hyp hyp={h} mvarId={goal.mvarId} key={i} />)}</div> }
    { assumptionHyps.length > 0 &&
      <div className="hyp-group">
        <div className="hyp-group-title">{t("Assumptions") + ":"}</div>
        {assumptionHyps.map((h, i) => <Hyp hyp={h} mvarId={goal.mvarId} key={i} />)}
      </div> }
  </div>
})

export const OtherGoals = React.memo((props: GoalProps2) => {
  let { t } = useTranslation()
  const { goals, filter } = props
  return <>
    {goals && goals.length > 1 &&
      <div id="other-goals" className="other-goals">
        <div className="goals-section-title">{t("Further Goals")}</div>
        {goals.slice(1).map((goal, i) =>
          <details key={i}>
            <summary>
              <InteractiveCode fmt={goal.type} />
            </summary>
            <Goal typewriter={false} filter={filter} goal={goal} />
          </details>)}
      </div>}
  </>
})

interface GoalsProps {
    goals: InteractiveGoalsWithHints
    filter: GoalFilterState
}

export function Goals({ goals, filter }: GoalsProps) {
    if (goals.goals.length === 0) {
        return <></>
    } else {
        return <>
          {goals.goals.map((g, i) => <Goal typewriter={false} key={i} goal={g.goal} filter={filter} />)}
        </>
    }
}

interface FilteredGoalsProps {
    /** Components to render in the header. */
    headerChildren: React.ReactNode
    /**
     * When this is `undefined`, the component will not appear at all but will remember its state
     * by virtue of still being mounted in the React tree. When it does appear again, the filter
     * settings and collapsed state will be as before. */
    goals?: InteractiveGoalsWithHints
}

/**
 * Display goals together with a header containing the provided children as well as buttons
 * to control how the goals are displayed.
 */
export const FilteredGoals = React.memo(({ headerChildren, goals }: FilteredGoalsProps) => {
    const ec = React.useContext(EditorContext)

    const copyToCommentButton =
        <a className="link pointer mh2 dim codicon codicon-quote"
            data-id="copy-goal-to-comment"
            onClick={e => {
                e.preventDefault();
                if (goals) void ec.copyToComment(goalsWithHintsToString(goals))
            }}
            title="copy state to comment" />

    const [goalFilters, setGoalFilters] = React.useState<GoalFilterState>(
        { reverse: false, showType: true, showInstance: true, showHiddenAssumption: true, showLetValue: true });

    const sortClasses = 'link pointer mh2 dim codicon ' + (goalFilters.reverse ? 'codicon-arrow-up ' : 'codicon-arrow-down ');
    const sortButton =
        <a className={sortClasses} title="reverse list"
            onClick={_ => setGoalFilters(s => ({ ...s, reverse: !s.reverse }))} />

    const mkFilterButton = (filterFn: React.SetStateAction<GoalFilterState>, filledFn: (_: GoalFilterState) => boolean, name: string) =>
        <a className='link pointer tooltip-menu-content' onClick={_ => { setGoalFilters(filterFn) }}>
            <span className={'tooltip-menu-icon codicon ' + (filledFn(goalFilters) ? 'codicon-check ' : 'codicon-blank ')}>&nbsp;</span>
            <span className='tooltip-menu-text '>{name}</span>
        </a>
    const filterMenu = <span>
        {mkFilterButton(s => ({ ...s, showType: !s.showType }), gf => gf.showType, 'types')}
        <br/>
        {mkFilterButton(s => ({ ...s, showInstance: !s.showInstance }), gf => gf.showInstance, 'instances')}
        <br/>
        {mkFilterButton(s => ({ ...s, showHiddenAssumption: !s.showHiddenAssumption }), gf => gf.showHiddenAssumption, 'hidden assumptions')}
        <br/>
        {mkFilterButton(s => ({ ...s, showLetValue: !s.showLetValue }), gf => gf.showLetValue, 'let-values')}
    </span>

    const isFiltered = !goalFilters.showInstance || !goalFilters.showType || !goalFilters.showHiddenAssumption || !goalFilters.showLetValue
    const filterButton =
        <WithTooltipOnHover mkTooltipContent={() => filterMenu}>
            <a className={'link pointer mh2 dim codicon ' + (isFiltered ? 'codicon-filter-filled ': 'codicon-filter ')}/>
        </WithTooltipOnHover>

    return <div style={{display: goals !== undefined ? 'block' : 'none'}}>
        <details open>
            <summary className='mv2 pointer'>
                {headerChildren}
                <span className='fr'>{copyToCommentButton}{sortButton}{filterButton}</span>
            </summary>
            <div className='ml1'>
                {goals && <Goals goals={goals} filter={goalFilters}></Goals>}
            </div>
        </details>
    </div>
})

export function loadGoals(
  rpcSess: RpcSessionAtPos,
  uri: string,
  setProof: React.Dispatch<React.SetStateAction<ProofState>>,
  setCrashed: React.Dispatch<React.SetStateAction<Boolean>>) {
console.info('sending rpc request to load the proof state')

rpcSess.call('Game.getProofState', DocumentPosition.toTdpp({line: 0, character: 0, uri: uri})).then(
  (proof : ProofState) => {
    if (typeof proof !== 'undefined') {
      console.info(`received a proof state!`)
      console.log(proof)
      setProof(proof)
      setCrashed(false)
    } else {
      console.warn('received undefined proof state!')
      setCrashed(true)
      // setProof(undefined)
    }
  }
).catch((error) => {
  setCrashed(true)
  console.warn(error)
})
}


export function lastStepHasErrors (proof : ProofState): boolean {
  if (!proof?.steps.length) {return false}

  let diags = [...proof.steps[proof.steps.length - 1].diags, ...proof.diagnostics]

  return diags.some(
    (d) => (d.severity == DiagnosticSeverity.Error ) // || d.severity == DiagnosticSeverity.Warning
  )
}

export function isLastStepWithErrors (proof : ProofState, i: number): boolean {
  if (!proof?.steps.length) {return false}
  return (i == proof.steps.length - 1) && lastStepHasErrors(proof)
}
