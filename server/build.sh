#!/usr/bin/env sh

# Operate in the directory where this file is located
cd $(dirname $0)

# Build Adam
( rm -rf adam
  git clone https://github.com/hhu-adam/Robo adam/
  cd adam
  docker rmi adam:latest || true
  docker build \
    --rm -f Dockerfile -t adam:latest .
)

# Build NNG
( rm -rf nng
  git clone https://github.com/hhu-adam/NNG4 nng/
  cd nng
  docker rmi nng:latest || true
  docker build \
    --rm -f Dockerfile -t nng:latest .
)
