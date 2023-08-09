#/bin/bash

(exec bwrap\
  --ro-bind ../../lean4game /lean4game \
  --ro-bind ../../$1 /game \
  --ro-bind ~/.elan /elan \
  --ro-bind /usr /usr \
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
