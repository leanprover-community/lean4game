#!/usr/bin/env sh

# Operate in the directory where this file is located
cd $(dirname $0)

# Build elan image if not already present
docker build --pull --rm -f elan.Dockerfile -t elan:latest .

# Build adam
(cd adam && lake exe cache get && lake build)
docker rmi adam:latest || true
docker build \
  --build-arg GAME_DIR=adam \
  --rm -f server.Dockerfile -t adam:latest .

# Build NNG
(cd nng && lake build)
docker rmi nng:latest || true
docker build \
  --build-arg GAME_DIR=nng \
  --rm -f server.Dockerfile -t nng:latest .
