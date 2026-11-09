FROM mcr.microsoft.com/devcontainers/javascript-node:26-bookworm

# The game server (leangame) in the version of the game, e.g. `v4.35.0` for
# `leanprover/lean4:v4.35.0`. It finds the game as a sibling folder in `/workspaces`, which only
# root can write to. Docker caches this step: after a tag has moved, rebuild without cache.
COPY lean-toolchain /tmp/lean-toolchain
RUN version="$(sed -E 's/.*:(v[0-9.]+).*/\1/' /tmp/lean-toolchain)" \
  && git clone --depth 1 --branch "$version" https://github.com/hhu-adam/leangame.git /workspaces/leangame \
  && chown -R node:node /workspaces/leangame

USER node

# the browser for the tests of the game server is not needed
RUN cd /workspaces/leangame && CYPRESS_INSTALL_BINARY=0 npm ci && npm cache clean --force

# install elan and the Lean toolchain of the game
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf \
  | sh -s -- -y --default-toolchain "$(cat /tmp/lean-toolchain)"
ENV PATH="/home/node/.elan/bin:${PATH}"
