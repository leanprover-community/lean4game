import * as React from 'react'

import {
    InteractiveGoal,
    InteractiveTermGoal,
    RpcSessionAtPos,
    UserWidgetInstance,
    Widget_getWidgetSource,
} from '@leanprover/infoview-api'
import { EnvPosContext } from './contexts'
import { ErrorBoundary } from './errors'
import { GoalsLocation } from './goalLocation'
import { useRpcSession } from './rpcSessions'
import { DocumentPosition, mapRpcError, useAsyncPersistent } from './util'

async function dynamicallyLoadModule(hash: string, code: string): Promise<any> {
    const file = new File([code], `widget_${hash}.js`, { type: 'text/javascript' })
    const url = URL.createObjectURL(file)
    return await import(url)
}

const moduleCache = new Map<string, any>()

/**
 * Fetch source code from Lean and dynamically import it as a JS module.
 *
 * The source must hash to `hash` (in Lean) and must have been annotated with `@[widget]`
 * or `@[widget_module]` at some point before `pos`. */
export async function importWidgetModule(rs: RpcSessionAtPos, pos: DocumentPosition, hash: string): Promise<any> {
    if (moduleCache.has(hash)) {
        // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
        return moduleCache.get(hash)!
    }
    const resp = await Widget_getWidgetSource(rs, pos, hash)
    const mod = await dynamicallyLoadModule(hash, resp.sourcetext)
    moduleCache.set(hash, mod)
    return mod
}

export interface DynamicComponentProps {
    hash: string
    props: any
    /** @deprecated set {@link EnvPosContext} instead */
    pos?: DocumentPosition
}

/**
 * Use {@link importWidgetModule} to import a module
 * which must `export default` a React component,
 * and render that with `props`.
 * Errors in the component are caught in an error boundary.
 *
 * The {@link EnvPosContext} must be set.
 * It is used to retrieve the `Lean.Environment`
 * from which the widget module identified by `hash`
 * is obtained.
 */
export function DynamicComponent(props_: React.PropsWithChildren<DynamicComponentProps>) {
    const { hash, props, children } = props_
    const rs = useRpcSession()
    const pos = React.useContext(EnvPosContext)
    const state = useAsyncPersistent(() => {
        if (!pos) throw new Error('position context is not set')
        return importWidgetModule(rs, pos, hash)
    }, [rs, pos, hash])
    return (
        <React.Suspense fallback={`Loading component '${hash}'..`}>
            <ErrorBoundary>
                {state.state === 'resolved' && React.createElement(state.value.default, props, children)}
                {state.state === 'rejected' && <span className="red">Error: {mapRpcError(state.error).message}</span>}
            </ErrorBoundary>
        </React.Suspense>
    )
}

interface PanelWidgetDisplayProps {
    pos: DocumentPosition
    goals: InteractiveGoal[]
    termGoal?: InteractiveTermGoal
    selectedLocations: GoalsLocation[]
    widget: UserWidgetInstance
}

/** Props that every infoview panel widget receives as input to its `default` export. */
export interface PanelWidgetProps {
    /** Cursor position in the file at which the widget is being displayed. */
    pos: DocumentPosition
    /** The current tactic-mode goals. */
    goals: InteractiveGoal[]
    /** The current term-mode goal, if any. */
    termGoal?: InteractiveTermGoal
    /** Locations currently selected in the goal state. */
    selectedLocations: GoalsLocation[]
}

export function PanelWidgetDisplay({ pos, goals, termGoal, selectedLocations, widget }: PanelWidgetDisplayProps) {
    const componentProps: PanelWidgetProps = { pos, goals, termGoal, selectedLocations, ...widget.props }
    return <DynamicComponent hash={widget.javascriptHash} props={componentProps} />
}
