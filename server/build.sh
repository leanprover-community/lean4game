#!/usr/bin/env sh

# Operate in the directory where this file is located
cd $(dirname $0)

# Build elan image if not already present
docker build --pull --rm -f elan.Dockerfile -t elan:latest .

# Build testgame
(cd testgame && lake exe cache get && lake build)
docker rmi testgame:latest || true
docker build \
  --build-arg GAME_DIR=testgame \
  --rm -f server.Dockerfile -t testgame:latest .

# Build NNG
(cd nng && lake build)
docker rmi nng:latest || true
docker build \
  --build-arg GAME_DIR=nng \
  --rm -f server.Dockerfile -t nng:latest .
