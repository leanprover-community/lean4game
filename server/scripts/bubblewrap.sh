#!/bin/bash

set -euo pipefail

# Limit CPU time per process to 1h
ulimit -t 3600
# NB: The RSS limit (ulimit -m) is not supported by modern linux!
# Usage: bubblewrap.sh GAME_DIR [BWRAP_OPTIONS...] -- COMMAND...
GAME_DIR="$(realpath "$1")"
shift # remove $1 from the arguments
LEAN_ROOT="$(cd "$GAME_DIR" && lean --print-prefix)"

BWRAP_OPTS=()
while [ "$#" -gt 0 ] && [ "$1" != "--" ]; do
  BWRAP_OPTS+=("$1")
  shift
done
shift # remove the `--`

GAMESERVER_PATH="/game"

# Docker forbids mounting a fresh procfs; BWRAP_BIND_PROC=true reuses the host's (read-only).
# The host's /proc doesn't match a new pid namespace (lean can't find its own executable),
# so we can't unshare the pid namespace in that case.
if [ "${BWRAP_BIND_PROC:-}" = "true" ]; then
  PROC_OPTS=(--ro-bind /proc /proc)
else
  PROC_OPTS=(--unshare-pid --proc /proc)
fi

exec bwrap \
  --ro-bind "$GAME_DIR" /game \
  --ro-bind "$LEAN_ROOT" /toolchain \
  --ro-bind /usr /usr \
  --ro-bind /etc/localtime /etc/localtime \
  --dev /dev \
  --tmpfs /tmp \
  "${PROC_OPTS[@]}" \
  --symlink usr/lib /lib \
  --symlink usr/lib64 /lib64 \
  --symlink usr/bin /bin \
  --symlink usr/sbin /sbin \
  --clearenv \
  --setenv PATH "/bin:/usr/bin:/toolchain/bin" \
  --setenv HOME /tmp \
  --unshare-user \
  --unshare-net \
  --unshare-uts \
  --unshare-cgroup \
  --die-with-parent \
  --chdir "$GAMESERVER_PATH" \
  "${BWRAP_OPTS[@]}" \
  "$@"
