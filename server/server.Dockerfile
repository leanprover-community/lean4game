FROM elan:latest

WORKDIR /

# Copy lean files
COPY leanserver ./leanserver
COPY testgame ./testgame
# TODO: make `testgame` a build argument

WORKDIR /leanserver
CMD ["./build/bin/gameserver", "TestGame", "../testgame"]