FROM ubuntu:noble

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        wget \
        git \
        openjdk-17-jre-headless \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /tlaplus

RUN wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

WORKDIR /work