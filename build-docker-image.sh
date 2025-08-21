#!/bin/bash

cd docker/
docker build . -t tlc
docker image save tlc > docker-tlc-image.tar
