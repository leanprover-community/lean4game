import type { Disposable } from 'vscode-languageserver-protocol'

export class EventEmitter<E, in out K> {
    private freshId: number = 0
    private handlers = new Map<number, (_: E) => void>()
    private handlersWithKey = new Map<K, ((_: E) => void)[]>()
    current?: E

    /**
     * Register a handler that will receive events from this emitter
     * and return a closure that removes the handler registration.
     *
     * If `key` is specified, only events fired with that key
     * will be propagated to this handler.
     */
    on(handler: (_: E) => void, key?: K): Disposable {
        const id = this.freshId
        this.freshId += 1
        if (key) {
            const handlersForKey = this.handlersWithKey.get(key) ?? []
            handlersForKey.push(handler)
            this.handlersWithKey.set(key, handlersForKey)
        } else {
            this.handlers.set(id, handler)
        }
        return {
            dispose: () => {
                if (key) {
                    const handlersForKey = this.handlersWithKey.get(key) ?? []
                    // We assume that no key has so many handlers registered
                    // that the linear `filter` operation becomes a perf issue.
                    this.handlersWithKey.set(
                        key,
                        handlersForKey.filter(h => h !== handler),
                    )
                } else {
                    this.handlers.delete(id)
                }
            },
        }
    }

    /**
     * Propagate the event to registered handlers.
     *
     * The event is propagated to all keyless handlers.
     * Furthermore if `key` is provided,
     * the event is also propagated to handlers registered with that key.
     */
    fire(event: E, key?: K): void {
        this.current = event
        for (const h of this.handlers.values()) {
            h(event)
        }
        if (key) {
            const handlersForKey = this.handlersWithKey.get(key) ?? []
            for (const h of handlersForKey) {
                h(event)
            }
        }
    }
}

type ExcludeNonEvent<T, U> = T extends (...args: any) => Promise<void> ? U : never

/**
 * Turn all fields in `T` which extend `(...args: As) => Promise<void>`
 * into event emitter fields `f: EventEmitter<As>`.
 * Other fields are removed.
 */
export type Eventify<T> = {
    [P in keyof T as ExcludeNonEvent<T[P], P>]: T[P] extends (arg: infer A) => Promise<void>
        ? EventEmitter<A, never>
        : T[P] extends (...args: infer As) => Promise<void>
          ? EventEmitter<As, never>
          : never
}
