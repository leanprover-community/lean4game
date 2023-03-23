#!/usr/bin/env sh

# Operate in the directory where this file is located
cd $(dirname $0)

cd server

cd testgame
lake update

cp lake-packages/mathlib/lean-toolchain lean-toolchain
cp lake-packages/mathlib/lean-toolchain ../leanserver/lean-toolchain
cp lake-packages/mathlib/lean-toolchain ../nng/lean-toolchain

cd ../leanserver
lake update

cd ../nng
lake update
