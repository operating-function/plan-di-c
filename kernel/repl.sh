#!/usr/bin/env bash

set -ex

gcc -O3 -Wall -Werror -lm plan.c bsdnt.c -o ./plan

cat sire.sire /dev/stdin | ./plan
