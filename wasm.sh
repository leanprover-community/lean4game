#!/bin/bash

rm -rf server32bit
cp -r server server32bit

cd server32bit
/home/alex/Projects/lean4/build/test/stage1/bin/lake update -R
/home/alex/Projects/lean4/build/test/stage1/bin/lake clean
/home/alex/Projects/lean4/build/test/stage1/bin/lake build

cd ../server

lake build


OUT_DIR=../client/public
LEAN_SYSROOT=/home/alex/Projects/lean4/build/release/stage1
LEAN_LIBDIR=$LEAN_SYSROOT/lib/lean

emcc -o $OUT_DIR/server.js main.c -I $LEAN_SYSROOT/include -L $LEAN_LIBDIR build/ir/GameServer/*.c -lInit -lLean -lleancpp -lleanrt \
  -sFORCE_FILESYSTEM -lnodefs.js -s EXIT_RUNTIME=0 -s MAIN_MODULE=1 -s LINKABLE=1 -s EXPORT_ALL=1 -s ALLOW_MEMORY_GROWTH=1 -fwasm-exceptions -pthread -flto \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Init"@/lib/Init \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Init.olean"@/lib/Init.olean \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Init.ilean"@/lib/Init.ilean \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Lean"@/lib/Lean \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Lean.olean"@/lib/Lean.olean \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Lean.ilean"@/lib/Lean.ilean \
  --preload-file "../server32bit/build/lib"@/gamelib
