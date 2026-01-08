#!/bin/bash

# Limit CPU time per process to 1h
ulimit -t 3600
# NB: The RSS limit (ulimit -m) is not supported by modern linux!

PROJECT_NAME="$(realpath $1)"
LEAN_ROOT="$(cd $1 && lean --print-prefix)"
LEAN_SRC_PATH=$(cd $1 && lake env printenv LEAN_SRC_PATH)

# $1 : the game directory
# $2 : does the game use a custom Lean server?
# $3 : additional bwrap options

if [ "$2" = "true" ]; then
  GAMESERVER_PATH="/game/.lake/packages/GameServer/server/.lake/build/bin/"
  GAMESERVER_CMD="./gameserver --server /game"
else
  GAMESERVER_PATH="/game"
  GAMESERVER_CMD="lake serve --"
fi

exec bwrap\
  --ro-bind "$1" /game \
  --ro-bind "$LEAN_ROOT" /lean \
  --ro-bind /usr /usr \
  --ro-bind /etc/localtime /etc/localtime \
  --dev /dev \
  --tmpfs /tmp \
  --proc /proc \
  --symlink usr/lib /lib\
  --symlink usr/lib64 /lib64\
  --symlink usr/bin /bin\
  --symlink usr/sbin /sbin\
  --clearenv \
  --setenv PATH "/bin:/usr/bin:/lean/bin" \
  --setenv LEAN_SRC_PATH "$LEAN_SRC_PATH" \
  --unshare-user \
  --unshare-pid  \
  --unshare-net  \
  --unshare-uts  \
  --unshare-cgroup \
  --die-with-parent \
  --chdir "$GAMESERVER_PATH" \
  $3 \
  $GAMESERVER_CMD
