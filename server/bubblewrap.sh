#/bin/bash

ELAN_HOME=$(lake env printenv ELAN_HOME)

# $1 : the game directory
# $2 : the lean4game folder
# $3 : the gameserver executable

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
  --chdir "/lean4game/server/.lake/build/bin/" \
  $3 --server /game
)
