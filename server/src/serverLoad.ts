import os from 'node:os'

import type { ApiServerLoad } from './api.js'

/** How often the CPU usage is sampled */
const CPU_SAMPLE_MS = 10_000

type CpuTimes = { busy: number; total: number }

function cpuTimes(): CpuTimes {
  let busy = 0
  let total = 0
  for (const { times } of os.cpus()) {
    const all = times.user + times.nice + times.sys + times.irq + times.idle
    busy += all - times.idle
    total += all
  }
  return { busy, total }
}

// `os.cpus()` only has cumulative counters, so the usage is the difference between two
// samples. Sampling in the background keeps the endpoint fast.
let lastTimes = cpuTimes()
let cpuUsage = 0
setInterval(() => {
  const times = cpuTimes()
  const total = times.total - lastTimes.total
  if (total > 0) cpuUsage = (times.busy - lastTimes.busy) / total
  lastTimes = times
}, CPU_SAMPLE_MS).unref()

/**
 * The share of the memory which is in use. Memory which the system can reclaim, like the
 * page cache, counts as available. Respects the cgroup limit when running in a container.
 */
function memoryUsage(): number {
  // `constrainedMemory` is a huge number when there is no limit
  const total = Math.min(process.constrainedMemory() || Infinity, os.totalmem())
  return 1 - Math.min(process.availableMemory(), total) / total
}

const clamp = (value: number) => Math.min(Math.max(value, 0), 1)

/** An indication of how busy the server is */
export function getServerLoad(): ApiServerLoad {
  return { memory: clamp(memoryUsage()), cpu: clamp(cpuUsage) }
}
