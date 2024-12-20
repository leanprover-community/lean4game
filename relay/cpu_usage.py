import time

def measure_proc_stat() -> dict[str, int]:
  proc_stat_header = open("/proc/stat", "r").readline()
  proc_stat = proc_stat_header.split(' ')[2:]
  proc_stat[-1] = proc_stat[-1].removesuffix('\n')
  proc_stat = list(map(int, proc_stat))

  proc_stat_dict= {'user': proc_stat[0],
                   'nice': proc_stat[1],
                   'system': proc_stat[2],
                   'idle': proc_stat[3],
                   'iowait': proc_stat[4],
                   'irq': proc_stat[5],
                   'softirq': proc_stat[6],
                   'steal': proc_stat[7],
                   'guest': proc_stat[8],
                   'guest_nice': proc_stat[9]}

  return proc_stat_dict

if __name__ == "__main__":
  """
  Script emulates htop calculation of CPU at the
  moment of calling.
  """
  prev = measure_proc_stat()
  prev_idle = prev.get('idle') + prev.get('iowait')
  prev_non_idle = prev.get('user') + prev.get('nice') + prev.get('system') + prev.get('irq') + prev.get('softirq') + prev.get('steal')
  prev_total = prev_idle + prev_non_idle

  time.sleep(0.1)

  curr = measure_proc_stat()
  curr_idle = curr.get('idle') + curr.get('iowait')
  curr_non_idle = curr.get('user') + curr.get('nice') + curr.get('system') + curr.get('irq') + curr.get('softirq') + curr.get('steal')
  curr_total = curr_idle + curr_non_idle

  d_total = curr_total - prev_total
  d_idle = curr_idle - prev_idle

  cpu_usage = ((d_total - d_idle)/d_total) * 100
  print(round(cpu_usage, 20))
