#!/usr/bin/env sh

# Operate in the directory where this file is located
cd $(dirname $0)

# Build elan image if not already present
docker build --pull --rm -f elan.Dockerfile -t elan:latest .

(cd testgame && lake exe cache get && lake build)
docker rmi testgame:latest || true
docker build --rm -f server.Dockerfile -t testgame:latest .
