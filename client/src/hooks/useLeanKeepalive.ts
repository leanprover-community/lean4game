import { useAtomValue } from 'jotai'
import { useEffect } from 'react'

import { leanInstanceAtom } from '../state/proof-atoms'

/** Time between keepalives of the Lean instance, the server stops it after 5 idle minutes */
const KEEPALIVE_MS = 60_000

/** Keeps the Lean instance of the game running, and restarts it if it is gone */
export function useLeanKeepalive() {
  const { data, refetch } = useAtomValue(leanInstanceAtom)
  const id = data?.id
  useEffect(() => {
    if (!id) return
    const interval = setInterval(() => {
      void fetch(`/api/lean/instances/${id}/keepalive`, {
        method: 'POST',
      }).then(res => {
        if (res.status === 404) void refetch()
      })
    }, KEEPALIVE_MS)
    return () => clearInterval(interval)
  }, [id, refetch])
}
