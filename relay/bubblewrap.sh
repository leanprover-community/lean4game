#/bin/bash

# Note: This fails if there is no default toolchain installed
LEAN_ROOT="$(cd $1 && lean --print-prefix)"
LEAN_PATH="$(cd $1 && lake env printenv LEAN_PATH)"

# $1 : the game directory
# $2 : the lean4game folder
# $3 : the gameserver executable

# # print commands as they are executed
# set -x

(exec bwrap\
  --ro-bind $2 /lean4game \
  --ro-bind $1 /game \
  --ro-bind "$LEAN_ROOT" /lean \
  --ro-bind /usr /usr \
  --dev /dev \
  --proc /proc \
  --symlink usr/lib /lib\
  --symlink usr/lib64 /lib64\
  --symlink usr/bin /bin\
  --symlink usr/sbin /sbin\
  --clearenv \
  --setenv PATH "/lean/bin" \
  --setenv LAKE "/no" `# tries to invoke git otherwise` \
  --setenv LEAN_PATH "$LEAN_PATH" \
  --unshare-user \
  --unshare-pid  \
  --unshare-net  \
  --unshare-uts  \
  --unshare-cgroup \
  --die-with-parent \
  --chdir "/game/.lake/packages/GameServer/server/.lake/build/bin/" \
  ./gameserver --server /game
)

# TODO
# --chdir "/game/.lake/packages/GameServer/server/.lake/build/bin/" \
# ./gameserver --server /game
