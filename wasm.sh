#!/bin/bash


cd server

lake build


OUT_DIR=../client/public
LEAN_SYSROOT=/home/alex/Projects/lean4/build/release/stage1
LEAN_LIBDIR=$LEAN_SYSROOT/lib/lean

emcc -o $OUT_DIR/server.js main.c -I $LEAN_SYSROOT/include -L $LEAN_LIBDIR build/ir/GameServer/*.c -lInit -lLean -lleancpp -lleanrt \
  -sFORCE_FILESYSTEM -lnodefs.js -s EXIT_RUNTIME=0 -s MAIN_MODULE=1 -s LINKABLE=1 -s EXPORT_ALL=1 -s ALLOW_MEMORY_GROWTH=1 -fwasm-exceptions -pthread -flto
