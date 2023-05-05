#!/usr/bin/env sh

# Operate in the directory where this file is located
cd $(dirname $0)

# TODO: Pull prebuilt docker images from GitHub

# Build elan image if not already present
docker build --pull --rm -f elan.Dockerfile -t elan:latest .

# Build Adam
( rm -rf adam
  git clone https://github.com/hhu-adam/Robo adam/
  cd adam
  lake exe cache get
  lake build)
docker rmi adam:latest || true
docker build \
  --build-arg GAME_DIR=adam \
  --rm -f server.Dockerfile -t adam:latest .

# Build NNG
( rm -rf nng
  git clone https://github.com/hhu-adam/NNG4 nng/
  cd nng
  lake exe cache get
  lake build)
docker rmi nng:latest || true
docker build \
  --build-arg GAME_DIR=nng \
  --rm -f server.Dockerfile -t nng:latest .
