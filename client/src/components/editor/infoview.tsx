import { InteractiveDiagnostics_msgToInteractive, MessageData } from '@leanprover/infoview-api'
import { useRpcSession } from './infoview/rpcSessions'
import { InteractiveMessage } from './infoview/traceExplorer'
import { mapRpcError, useAsync } from './infoview/util'

export * from '@leanprover/infoview-api'
export { EditorContext, EnvPosContext, VersionContext } from './infoview/contexts'
export { EditorConnection } from './infoview/editorConnection'
export { GoalLocation, GoalsLocation, LocationsContext } from './infoview/goalLocation'
export { InteractiveCode, /*InteractiveCodeProps*/ } from './infoview/interactiveCode'
export { renderInfoview } from './infoview/main'
export { RpcContext, useRpcSession } from './infoview/rpcSessions'
export { ServerVersion } from './infoview/serverVersion'
export { DynamicComponent, /*DynamicComponentProps, PanelWidgetProps,*/ importWidgetModule } from './infoview/userWidget'
export {
    DocumentPosition,
    mapRpcError,
    useAsync,
    useAsyncPersistent,
    useAsyncWithTrigger,
    useClientNotificationEffect,
    useClientNotificationState,
    useEvent,
    useEventResult,
    useServerNotificationEffect,
    useServerNotificationState,
} from './infoview/util'
// export { MessageData }

/** Display the given message data as interactive, pretty-printed text. */
export function InteractiveMessageData({ msg }: { msg: MessageData }) {
    const rs = useRpcSession()
    const interactive = useAsync(() => InteractiveDiagnostics_msgToInteractive(rs, msg, 0), [rs, msg])

    if (interactive.state === 'resolved') {
        return <InteractiveMessage fmt={interactive.value} />
    } else if (interactive.state === 'loading') {
        return <>...</>
    } else {
        return (
            <div>
                Failed to display message:
                {<span>{mapRpcError(interactive.error).message}</span>}
            </div>
        )
    }
}
