#!/usr/bin/env bash
# Builds the game once the devcontainer is created. If the game depends on mathlib, the
# prebuilt mathlib is downloaded first, building it from scratch would take hours.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# fails if the game doesn't depend on mathlib, which only has the executable `cache`
if ! lake exe cache get; then
  # the dependencies have been fetched by now
  if [ -d .lake/packages/mathlib ]; then
    echo "Downloading the prebuilt mathlib failed, not building it from scratch." >&2
    echo "Run \`lake exe cache get\` and then \`lake build\` to try again." >&2
    exit 1
  fi
  echo "The game doesn't depend on mathlib, nothing to download."
fi

lake build
