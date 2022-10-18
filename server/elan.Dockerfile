FROM ubuntu:18.04

WORKDIR /

RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y git curl

# Install elan
RUN curl -sSfL https://github.com/leanprover/elan/releases/download/v1.4.2/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
RUN ./elan-init -y --default-toolchain leanprover/lean4:nightly-2022-09-23
# TODO: Read out lean version from lean-toolchain file
ENV PATH="${PATH}:/root/.elan/bin"
