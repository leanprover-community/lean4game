/**
 * Traces of any substantial compilation or elaboration process are usually extremely verbose,
 * which makes them slow (or even infeasible) to pretty-print and difficult to understand.
 * Instead, we provide a "TraceExplorer" UI which allows users to lazily expand trace subtrees,
 * and (TODO) execute search queries.
 *
 * @module
 */

import {
    InteractiveDiagnostics_msgToInteractive,
    lazyTraceChildrenToInteractive,
    MessageData,
    MsgEmbed,
    TraceEmbed,
} from '@leanprover/infoview-api'
import * as React from 'react'
import { Goal } from './goals'
import {
    InteractiveCode,
    InteractiveTaggedText,
    InteractiveTagProps,
    InteractiveTextComponentProps,
} from './interactiveCode'
import { useRpcSession } from './rpcSessions'
import { DynamicComponent } from './userWidget'
import { mapRpcError, useAsyncWithTrigger } from './util'

function LazyTrace({ col, cls, msg }: { col: number; cls: string; msg: MessageData }) {
    const rs = useRpcSession()

    const [tt, fetchTrace] = useAsyncWithTrigger(
        () => InteractiveDiagnostics_msgToInteractive(rs, msg, col),
        [rs, msg, col],
    )

    const [open, setOpen] = React.useState(false)

    if (!open)
        return (
            <span
                className="underline-hover pointer"
                onClick={ev => {
                    void fetchTrace()
                    setOpen(true)
                    ev.stopPropagation()
                    ev.preventDefault()
                }}
            >
                [{cls}] &gt;
            </span>
        )
    else if (tt.state === 'resolved')
        return (
            <>
                <span
                    className="underline-hover pointer"
                    onClick={ev => {
                        setOpen(false)
                        ev.stopPropagation()
                        ev.preventDefault()
                    }}
                >
                    [{cls}] ∨
                </span>
                <InteractiveMessage fmt={tt.value} />
            </>
        )
    else if (tt.state === 'rejected')
        return (
            <>
                <span
                    className="underline-hover pointer"
                    onClick={ev => {
                        void fetchTrace()
                        ev.stopPropagation()
                        ev.preventDefault()
                    }}
                >
                    [{cls}] Error (click to retry):
                </span>{' '}
                {mapRpcError(tt.error)}
            </>
        )
    else return <span>[{cls}] Loading..</span>
}

const TraceClassContext = React.createContext<string>('')

function abbreviateCommonPrefix(parent: string, cls: string): string {
    const parentParts = parent.split('.')
    const clsParts = cls.split('.')
    let i = 0
    for (; i < parentParts.length && i < clsParts.length && parentParts[i] === clsParts[i]; i++);
    return clsParts.slice(i).join('.')
}

function TraceLine({ indent, cls, msg, icon }: TraceEmbed & { icon: string }) {
    const spaces = ' '.repeat(indent)
    const abbrCls = abbreviateCommonPrefix(React.useContext(TraceClassContext), cls)
    return (
        <div className="trace-line">
            {spaces}
            <span className="trace-class" title={cls}>
                [{abbrCls}]
            </span>{' '}
            <InteractiveMessage fmt={msg} /> {icon}
        </div>
    )
}

function ChildlessTraceNode(traceEmbed: TraceEmbed) {
    return <TraceLine {...traceEmbed} icon="" />
}

function CollapsibleTraceNode(traceEmbed: TraceEmbed) {
    const { cls, collapsed: collapsedByDefault, children: lazyKids } = traceEmbed

    const rs = useRpcSession()
    const [children, fetchChildren] = useAsyncWithTrigger(async () => {
        if ('strict' in lazyKids) {
            return lazyKids.strict
        } else {
            return lazyTraceChildrenToInteractive(rs, lazyKids.lazy)
        }
    }, [rs, lazyKids])

    const [open, setOpen] = React.useState(!collapsedByDefault) // TODO: reset when collapsedByDefault changes?
    if (open && children.state === 'notStarted') void fetchChildren()
    let icon = open ? '▼' : '▶'
    if (children.state === 'loading') icon += ' ⋯'

    const onClick = React.useCallback(
        (ev: React.MouseEvent) => {
            if (!(ev.target instanceof Node)) return
            if (!ev.currentTarget || !ev.target) return
            // Don't handle clicks within React portals nested in this div (notably, tooltips).
            if (!ev.currentTarget.contains(ev.target)) return
            ev.stopPropagation()
            ev.preventDefault()
            if (!open) void fetchChildren()
            setOpen(o => !o)
        },
        [open, fetchChildren],
    )

    return (
        <div>
            <div className="pointer" onClick={onClick}>
                <TraceLine {...traceEmbed} icon={icon} />
            </div>
            <div style={{ display: open ? 'block' : 'none' }}>
                <TraceClassContext.Provider value={cls}>
                    {children.state === 'resolved' ? (
                        children.value.map((tt, i) => <InteractiveMessage fmt={tt} key={i} />)
                    ) : children.state === 'rejected' ? (
                        mapRpcError(children.error).toString()
                    ) : (
                        <></>
                    )}
                </TraceClassContext.Provider>
            </div>
        </div>
    )
}

function Trace(traceEmbed: TraceEmbed) {
    const noChildren = 'strict' in traceEmbed.children && traceEmbed.children.strict.length === 0
    return noChildren ? <ChildlessTraceNode {...traceEmbed} /> : <CollapsibleTraceNode {...traceEmbed} />
}

function InteractiveMessageTag({ tag: embed }: InteractiveTagProps<MsgEmbed>): JSX.Element {
    if ('expr' in embed) return <InteractiveCode fmt={embed.expr} />
    else if ('goal' in embed)
        return (
            <Goal
                goal={embed.goal}
                filter={{
                    reverse: false,
                    showType: true,
                    showInstance: true,
                    showHiddenAssumption: true,
                    showLetValue: true,
                }}
                additionalClassNames=""
            />
        )
    else if ('widget' in embed)
        return <DynamicComponent hash={embed.widget.wi.javascriptHash} props={embed.widget.wi.props} />
    else if ('lazyTrace' in embed)
        return <LazyTrace col={embed.lazyTrace[0]} cls={embed.lazyTrace[1]} msg={embed.lazyTrace[2]} />
    else if ('trace' in embed) return <Trace {...embed.trace} />
    else return <div>malformed MsgEmbed: {JSON.stringify(embed)}</div>
}

export function InteractiveMessage({ fmt }: InteractiveTextComponentProps<MsgEmbed>) {
    return InteractiveTaggedText({ fmt, InnerTagUi: InteractiveMessageTag })
}
