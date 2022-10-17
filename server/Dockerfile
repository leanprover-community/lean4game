FROM ubuntu:18.04

WORKDIR /

RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y git curl

# Install elan
RUN curl -sSfL https://github.com/leanprover/elan/releases/download/v1.4.2/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
RUN ./elan-init -y --default-toolchain leanprover/lean4:stable
ENV PATH="${PATH}:/root/.elan/bin"

# clone repos
RUN git clone https://github.com/hhu-adam/lean4-game-server.git game-server
RUN cd game-server && git checkout gvisor
RUN cd game-server && lake build

RUN git clone https://github.com/hhu-adam/NNG4.git

WORKDIR /NNG4

RUN git checkout gvisor
RUN lake build
CMD ["./build/bin/nng"]