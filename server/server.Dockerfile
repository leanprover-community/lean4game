ARG GAME_DIR
FROM elan:latest

WORKDIR /

# Copy lean files
COPY leanserver ./leanserver
COPY $GAME_DIR ./$GAME_DIR
# TODO: make `testgame` a build argument

WORKDIR /leanserver
RUN rm -f ./build/bin/gameserver
RUN lake build

WORKDIR /leanserver/build/bin/
