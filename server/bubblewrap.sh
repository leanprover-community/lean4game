#/bin/bash

ELAN_HOME=$(lake env printenv ELAN_HOME)

(exec bwrap\
  --bind ../../lean4game /lean4game \
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
  --chdir "/lean4game/server/build/bin/" \
  ./gameserver --server /game
)
