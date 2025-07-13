#/bin/bash

# Note: This fails if there is no default toolchain installed
ELAN_HOME=$(lake env printenv ELAN_HOME)

# $1 : the game directory
# $2 : the lean4game folder
# $3 : does the game use a custom Lean server?

if [ "$3" = "true" ]; then
  GAMESERVER_PATH="/game/.lake/packages/GameServer/server/.lake/build/bin/"
  GAMESERVER_CMD="./gameserver --server /game"
else
  GAMESERVER_PATH="/game"
  GAMESERVER_CMD="lake serve --"
fi

(exec bwrap\
  --bind $2 /lean4game \
  --bind $1 /game \
  --bind $ELAN_HOME /elan \
  --bind /usr /usr \
  --dev /dev \
  --proc /proc \
  --symlink usr/lib /lib\
  --symlink usr/lib64 /lib64\
  --symlink usr/bin /bin\
  --symlink usr/sbin /sbin\
  --clearenv \
  --setenv PATH "/elan/bin:/bin" \
  --setenv ELAN_HOME "/elan" \
  --unshare-user \
  --unshare-pid  \
  --unshare-net  \
  --unshare-uts  \
  --unshare-cgroup \
  --die-with-parent \
  --chdir "$GAMESERVER_PATH" \
  $GAMESERVER_CMD
)
