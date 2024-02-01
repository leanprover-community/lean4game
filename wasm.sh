#!/bin/bash

cd server

mkdir -p .lake/toolchains
if [ ! -f .lake/toolchains/lean-4.3.0-rc2-linux_wasm32.tar.zst  ]
then
    wget -P .lake/toolchains https://github.com/leanprover/lean4/releases/download/v4.3.0-rc2/lean-4.3.0-rc2-linux_wasm32.tar.zst
    tar --use-compress-program=unzstd -xvf .lake/toolchains/lean-4.3.0-rc2-linux_wasm32.tar.zst -C .lake/toolchains
fi
if [ ! -f .lake/toolchains/lean-4.3.0-rc2-linux_x86.tar.zst  ]
then
    wget -P .lake/toolchains https://github.com/leanprover/lean4/releases/download/v4.3.0-rc2/lean-4.3.0-rc2-linux_x86.tar.zst
    tar --use-compress-program=unzstd -xvf .lake/toolchains/lean-4.3.0-rc2-linux_x86.tar.zst -C .lake/toolchains
fi

# Linking will fail, but that's ok. We only need the c files.
.lake/toolchains/lean-4.3.0-rc2-linux_x86/bin/lake build -f=lakefile32.lean


lake build


OUT_DIR=../client/public
LEAN_SYSROOT=.lake/toolchains/lean-4.3.0-rc2-linux_wasm32
LEAN_LIBDIR=$LEAN_SYSROOT/lib/lean

emcc -o $OUT_DIR/server.js main.c -I $LEAN_SYSROOT/include -L $LEAN_LIBDIR .lake/build/ir/GameServer/*.c -lInit -lLean -lleancpp -lleanrt \
  -sFORCE_FILESYSTEM -lnodefs.js -s EXIT_RUNTIME=0 -s MAIN_MODULE=1 -s LINKABLE=1 -s EXPORT_ALL=1 -s ALLOW_MEMORY_GROWTH=1 -fwasm-exceptions -pthread -flto \
  -sPTHREAD_POOL_SIZE_STRICT=2 \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Init"@/lib/Init \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Init.olean"@/lib/Init.olean \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Init.ilean"@/lib/Init.ilean \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Lean"@/lib/Lean \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Lean.olean"@/lib/Lean.olean \
  --preload-file "${LEAN_SYSROOT}/lib/lean/Lean.ilean"@/lib/Lean.ilean \
  --preload-file "./.lake/build32/lib"@/gamelib
