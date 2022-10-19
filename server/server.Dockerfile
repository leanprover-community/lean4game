FROM elan:latest

WORKDIR /

# Copy lean files
COPY leanserver ./leanserver
COPY testgame ./testgame
# TODO: make `testgame` a build argument

WORKDIR /leanserver
RUN rm -f ./build/bin/gameserver
RUN lake build
CMD ["./build/bin/gameserver", "TestGame", "../testgame"]