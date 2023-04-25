ARG GAME_DIR
FROM elan:latest

WORKDIR /

# Copy lean files
COPY GameServer ./GameServer
COPY Main.lean ./Main
COPY lakefile.lean ./lakefile.lean
COPY lake-manifest.lean ./lake-manifest.lean
COPY lean-toolchain ./lean-toolchain
COPY $GAME_DIR ./$GAME_DIR
# TODO: make `adam` a build argument

WORKDIR /
RUN rm -f ./build/bin/gameserver
RUN lake build

WORKDIR /build/bin/
