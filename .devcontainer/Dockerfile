FROM mcr.microsoft.com/devcontainers/javascript-node:26-bookworm

USER root

# cypress dependencies: https://on.cypress.io/required-dependencies
# bubblewrap and python (for the scripts in `client/scripts`)
RUN apt-get update && apt-get install -y --no-install-recommends \
    libgtk-3-0 \
    libgbm-dev \
    libnotify-dev \
    libnss3 \
    libxss1 \
    libasound2 \
    libxtst6 \
    xauth \
    xvfb \
    bubblewrap \
    python3 \
    python3-venv \
    python-is-python3 \
    && rm -rf /var/lib/apt/lists/*

USER node

# install claude code
RUN npm install -g @anthropic-ai/claude-code
RUN npm cache clean --force

# install elan
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
ENV PATH="/home/node/.elan/bin:${PATH}"
