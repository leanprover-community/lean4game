import {
    InfoviewActionKind,
    InteractiveGoal,
    InteractiveGoals,
    InteractiveHypothesisBundle,
    InteractiveHypothesisBundle_nonAnonymousNames,
    MVarId,
    TaggedText_stripTags,
} from '@leanprover/infoview-api'
import * as React from 'react'
import { Details } from './collapsing'
import { ConfigContext, EditorContext } from './contexts'
import { Locations, LocationsContext, SelectableLocationSettings, useSelectableLocation } from './goalLocation'
import { useHoverHighlight } from './hoverHighlight'
import { InteractiveCode } from './interactiveCode'
import { WithTooltipOnHover } from './tooltips'
import { useEvent } from './util'

/** Returns true if `h` is inaccessible according to Lean's default name rendering. */
function isInaccessibleName(h: string): boolean {
    return h.indexOf('✝') >= 0
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
    return goals.goals.map(goalToString).join('\n\n')
}

interface GoalFilterState {
    /** If true reverse the list of hypotheses, if false present the order received from LSP. */
    reverse: boolean
    /** If true show hypotheses that have isType=True, otherwise hide them. */
    showType: boolean
    /** If true show hypotheses that have isInstance=True, otherwise hide them. */
    showInstance: boolean
    /** If true show hypotheses that contain a dagger in the name, otherwise hide them. */
    showHiddenAssumption: boolean
    /** If true show the bodies of let-values, otherwise hide them. */
    showLetValue: boolean
}

function getFilteredHypotheses(
    hyps: InteractiveHypothesisBundle[],
    filter: GoalFilterState,
): InteractiveHypothesisBundle[] {
    return hyps.reduce((acc: InteractiveHypothesisBundle[], h) => {
        if (h.isInstance && !filter.showInstance) return acc
        if (h.isType && !filter.showType) return acc
        const names = filter.showHiddenAssumption ? h.names : h.names.filter(n => !isInaccessibleName(n))
        const hNew: InteractiveHypothesisBundle = filter.showLetValue
            ? { ...h, names }
            : { ...h, names, val: undefined }
        if (names.length !== 0) acc.push(hNew)
        return acc
    }, [])
}

interface HypNameProps {
    name: string
    isInserted: boolean
    isRemoved: boolean
    mvarId?: string | undefined
    fvarId?: string | undefined
}

function HypName({ name, isInserted, isRemoved, mvarId, fvarId }: HypNameProps) {
    const ref = React.useRef<HTMLSpanElement>(null)

    const locs = React.useContext(LocationsContext)

    const hhl = useHoverHighlight({
        ref,
        highlightOnHover: locs !== undefined && mvarId !== undefined && fvarId !== undefined,
        underlineOnModHover: false,
    })

    let selectableLocationSettings: SelectableLocationSettings
    if (mvarId !== undefined && fvarId !== undefined) {
        selectableLocationSettings = { isSelectable: true, loc: { mvarId, loc: { hyp: fvarId } } }
    } else {
        selectableLocationSettings = { isSelectable: false }
    }
    const sl = useSelectableLocation(selectableLocationSettings)

    const namecls: string =
        (isInserted ? 'inserted-text ' : '') +
        (isRemoved ? 'removed-text ' : '') +
        (isInaccessibleName(name) ? 'goal-inaccessible ' : '') +
        hhl.className +
        sl.className
    return (
        <>
            <span
                ref={ref}
                className={namecls}
                onPointerOver={e => hhl.onPointerOver(e)}
                onPointerOut={e => hhl.onPointerOut(e)}
                onPointerMove={e => hhl.onPointerMove(e)}
                onClick={e => sl.onClick(e)}
                onPointerDown={e => sl.onPointerDown(e)}
            >
                {name}
            </span>
            &nbsp;
        </>
    )
}

interface HypProps {
    hyp: InteractiveHypothesisBundle
    mvarId?: MVarId
}

function Hyp({ hyp: h, mvarId }: HypProps) {
    const locs = React.useContext(LocationsContext)

    const names = InteractiveHypothesisBundle_nonAnonymousNames(h).map((n, i) => (
        <HypName
            name={n}
            isInserted={!!h.isInserted}
            isRemoved={!!h.isRemoved}
            mvarId={mvarId}
            fvarId={h.fvarIds?.at(i)}
            key={i}
        ></HypName>
    ))

    const typeLocs: Locations | undefined = React.useMemo(
        () =>
            locs && mvarId && h.fvarIds && h.fvarIds.length > 0
                ? { ...locs, subexprTemplate: { mvarId, loc: { hypType: [h.fvarIds[0], ''] } } }
                : undefined,
        [locs, mvarId, h.fvarIds],
    )

    const valLocs: Locations | undefined = React.useMemo(
        () =>
            h.val && locs && mvarId && h.fvarIds && h.fvarIds.length > 0
                ? { ...locs, subexprTemplate: { mvarId, loc: { hypValue: [h.fvarIds[0], ''] } } }
                : undefined,
        [h.val, locs, mvarId, h.fvarIds],
    )

    return (
        <div>
            <strong className="goal-hyp">{names}</strong>
            :&nbsp;
            <LocationsContext.Provider value={typeLocs}>
                <InteractiveCode fmt={h.type} />
            </LocationsContext.Provider>
            {h.val && (
                <LocationsContext.Provider value={valLocs}>
                    &nbsp;:=&nbsp;
                    <InteractiveCode fmt={h.val} />
                </LocationsContext.Provider>
            )}
        </div>
    )
}

interface GoalProps {
    goal: InteractiveGoal
    filter: GoalFilterState
    additionalClassNames: string
}

/**
 * Displays the hypotheses, target type and optional case label of a goal according to the
 * provided `filter`. */
export const Goal = React.memo((props: GoalProps) => {
    const { goal, filter, additionalClassNames } = props
    const config = React.useContext(ConfigContext)

    const prefix = goal.goalPrefix ?? '⊢ '
    const filteredList = getFilteredHypotheses(goal.hyps, filter)
    const hyps = filter.reverse ? filteredList.slice().reverse() : filteredList
    const locs = React.useContext(LocationsContext)
    const goalLocs = React.useMemo(
        () =>
            locs && goal.mvarId
                ? { ...locs, subexprTemplate: { mvarId: goal.mvarId, loc: { target: '' } } }
                : undefined,
        [locs, goal.mvarId],
    )
    const goalLi = (
        <div key={'goal'} data-is-goal>
            <strong className="goal-vdash">{prefix}</strong>
            <LocationsContext.Provider value={goalLocs}>
                <InteractiveCode fmt={goal.type} />
            </LocationsContext.Provider>
        </div>
    )

    let cn = 'font-code tl pre-wrap bl bw1 pl1 b--transparent mb3 ' + additionalClassNames
    if (props.goal.isInserted) cn += ' b--inserted '
    if (props.goal.isRemoved) cn += ' b--removed '

    const children: React.ReactNode[] = [
        filter.reverse && goalLi,
        hyps.map((h, i) => <Hyp hyp={h} mvarId={goal.mvarId} key={i} />),
        !filter.reverse && goalLi,
    ]

    if (goal.userName && config.showGoalNames) {
        return (
            <details open className={cn}>
                <summary className="mv1 pointer">
                    <strong className="goal-case">case </strong>
                    {goal.userName}
                </summary>
                {children}
            </details>
        )
    } else return <div className={cn}>{children}</div>
})

interface GoalsProps {
    goals: InteractiveGoals
    filter: GoalFilterState
    /** Whether or not to display the number of goals. */
    displayCount: boolean
}

function Goals({ goals, filter, displayCount }: GoalsProps) {
    const nGoals = goals.goals.length
    const config = React.useContext(ConfigContext)
    if (nGoals === 0) {
        return <strong className="db2 mb2 goal-goals">No goals</strong>
    } else {
        const unemphasizeCn = 'o-70 font-size-code-smaller'
        return (
            <>
                {displayCount && (
                    <strong className="db mb2 goal-goals">
                        {nGoals} {1 < nGoals ? 'goals' : 'goal'}
                    </strong>
                )}
                {goals.goals.map((g, i) => (
                    <Goal
                        key={i}
                        goal={g}
                        filter={filter}
                        additionalClassNames={i !== 0 && config.emphasizeFirstGoal ? unemphasizeCn : ''}
                    />
                ))}
            </>
        )
    }
}

interface FilteredGoalsProps {
    /** Components to render in the header. */
    headerChildren: React.ReactNode
    /**
     * When this is `undefined`, the component will not appear at all but will remember its state
     * by virtue of still being mounted in the React tree. When it does appear again, the filter
     * settings and collapsed state will be as before. */
    goals?: InteractiveGoals
    /** Whether or not to display the number of goals. */
    displayCount: boolean
    /** Whether the list of goals should be expanded on first render. */
    initiallyOpen: boolean
    /** If specified, the display will be toggled (collapsed/expanded) when this action is requested
     * by the user. */
    togglingAction?: InfoviewActionKind
}

/**
 * Display goals together with a header containing the provided children as well as buttons
 * to control how the goals are displayed.
 */
export const FilteredGoals = React.memo(
    ({ headerChildren, goals, displayCount, initiallyOpen, togglingAction }: FilteredGoalsProps) => {
        const ec = React.useContext(EditorContext)
        const config = React.useContext(ConfigContext)

        const copyToCommentButton = (
            <a
                className="link pointer mh2 dim codicon codicon-quote"
                data-id="copy-goal-to-comment"
                onClick={_ => {
                    if (goals) void ec.copyToComment(goalsToString(goals))
                }}
                title="copy state to comment"
            />
        )

        const [goalFilters, setGoalFilters] = React.useState<GoalFilterState>({
            reverse: config.reverseTacticState,
            showType: true,
            showInstance: true,
            showHiddenAssumption: true,
            showLetValue: true,
        })
        const sortClasses =
            'link pointer mh2 dim codicon ' + (goalFilters.reverse ? 'codicon-arrow-up ' : 'codicon-arrow-down ')
        const sortButton = (
            <a
                className={sortClasses}
                title="reverse list"
                onClick={_ => {
                    setGoalFilters(s => ({ ...s, reverse: !s.reverse }))
                }}
            />
        )

        const mkFilterButton = (
            filterFn: React.SetStateAction<GoalFilterState>,
            filledFn: (_: GoalFilterState) => boolean,
            name: string,
        ) => (
            <a
                className="link pointer tooltip-menu-content"
                onClick={_ => {
                    setGoalFilters(filterFn)
                }}
            >
                <span
                    className={
                        'tooltip-menu-icon codicon ' + (filledFn(goalFilters) ? 'codicon-check ' : 'codicon-blank ')
                    }
                >
                    &nbsp;
                </span>
                <span className="tooltip-menu-text ">{name}</span>
            </a>
        )
        const filterMenu = (
            <span>
                {mkFilterButton(
                    s => ({ ...s, showType: !s.showType }),
                    gf => gf.showType,
                    'types',
                )}
                <br />
                {mkFilterButton(
                    s => ({ ...s, showInstance: !s.showInstance }),
                    gf => gf.showInstance,
                    'instances',
                )}
                <br />
                {mkFilterButton(
                    s => ({ ...s, showHiddenAssumption: !s.showHiddenAssumption }),
                    gf => gf.showHiddenAssumption,
                    'hidden assumptions',
                )}
                <br />
                {mkFilterButton(
                    s => ({ ...s, showLetValue: !s.showLetValue }),
                    gf => gf.showLetValue,
                    'let-values',
                )}
            </span>
        )

        const isFiltered =
            !goalFilters.showInstance ||
            !goalFilters.showType ||
            !goalFilters.showHiddenAssumption ||
            !goalFilters.showLetValue
        const filterButton = (
            <WithTooltipOnHover tooltipChildren={filterMenu} className="dim ">
                <a
                    className={
                        'link pointer mh2 codicon ' + (isFiltered ? 'codicon-filter-filled ' : 'codicon-filter ')
                    }
                />
            </WithTooltipOnHover>
        )

        const setOpenRef = React.useRef<React.Dispatch<React.SetStateAction<boolean>>>()
        useEvent(
            ec.events.requestedAction,
            _ => {
                if (togglingAction !== undefined && setOpenRef.current !== undefined) {
                    setOpenRef.current(t => !t)
                }
            },
            [setOpenRef, togglingAction],
            togglingAction,
        )

        return (
            <div style={{ display: goals !== undefined ? 'block' : 'none' }}>
                <Details setOpenRef={r => (setOpenRef.current = r)} initiallyOpen={initiallyOpen}>
                    <>
                        {headerChildren}
                        <span
                            className="fr"
                            onClick={e => {
                                e.preventDefault()
                            }}
                        >
                            {copyToCommentButton}
                            {sortButton}
                            {filterButton}
                        </span>
                    </>
                    <div className="ml1">
                        {goals && <Goals goals={goals} filter={goalFilters} displayCount={displayCount}></Goals>}
                    </div>
                </Details>
            </div>
        )
    },
)
