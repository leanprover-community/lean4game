import * as React from 'react'
import { EditorContext } from '../../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/contexts'

export function useClientNotificationEffect<T>(method: string, f: (params: T) => void, deps?: React.DependencyList): void {
  const ec = React.useContext(EditorContext)
  React.useEffect(() => {
    let alive = true
    let subscribed = false

    void ec.api.subscribeClientNotifications(method).then(() => {
      subscribed = true
      if (!alive) {
        void ec.api.unsubscribeClientNotifications(method).catch((ex) => {
          console.warn(`Failed unsubscribing from client notification '${method}': ${ex}`)
        })
      }
    }).catch(ex => {
      console.error(`Failed subscribing to client notification '${method}': ${ex}`)
    })

    const h = ec.events.sentClientNotification.on(([thisMethod, params]: [string, T]) => {
      if (thisMethod !== method) return
      f(params)
    })

    return () => {
      alive = false
      h.dispose()
      if (subscribed) {
        void ec.api.unsubscribeClientNotifications(method).catch((ex) => {
          console.warn(`Failed unsubscribing from client notification '${method}': ${ex}`)
        })
      }
    }
  }, deps)
}

export function useServerNotificationEffect<T>(method: string, f: (params: T) => void, deps?: React.DependencyList): void {
  const ec = React.useContext(EditorContext)
  React.useEffect(() => {
    let alive = true
    let subscribed = false

    void ec.api.subscribeServerNotifications(method).then(() => {
      subscribed = true
      if (!alive) {
        void ec.api.unsubscribeServerNotifications(method).catch((ex) => {
          console.warn(`Failed unsubscribing from server notification '${method}': ${ex}`)
        })
      }
    }).catch(ex => {
      console.error(`Failed subscribing to server notification '${method}': ${ex}`)
    })

    const h = ec.events.gotServerNotification.on(([thisMethod, params]: [string, T]) => {
      if (thisMethod !== method) return
      f(params)
    })

    return () => {
      alive = false
      h.dispose()
      if (subscribed) {
        void ec.api.unsubscribeServerNotifications(method).catch((ex) => {
          console.warn(`Failed unsubscribing from server notification '${method}': ${ex}`)
        })
      }
    }
  }, deps)
}

export function useServerNotificationState<S, T>(
  method: string,
  initial: S,
  f: (params: T) => Promise<(state: S) => S>,
  deps?: React.DependencyList
): [S, React.Dispatch<React.SetStateAction<S>>] {
  const [s, setS] = React.useState<S>(initial)

  useServerNotificationEffect(method, (params: T) => {
    void f(params).then(g => setS(g))
  }, deps)

  return [s, setS]
}
