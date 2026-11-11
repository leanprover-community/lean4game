#!/usr/bin/env bash
# Starts the game server (leangame), which the Dockerfile installs next to the game, at
# http://localhost:3000. Runs when VS Code connects to the devcontainer. Stop it with Ctrl+C
# and start it again with `.devcontainer/start-server.sh`.
set -euo pipefail

GAME_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GAME="$(basename "$GAME_DIR" | tr '[:upper:]' '[:lower:]')"
URL="http://localhost:3000/g/local/$GAME"

# e.g. after reloading the window, the server may still be running
if curl --silent --fail --max-time 2 --output /dev/null http://localhost:3000; then
  echo "The game server is already running: $URL"
  exit 0
fi

echo "Starting the game server, the game will be at $URL"
echo "After changing the game, run \`lake build\` and reload the page."
cd /workspaces/leangame
exec npm start
