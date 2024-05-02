#!/usr/bin/env bash

set -ex

gcc -O3 -Wall -Werror -lm plan.c -o ./plan

./plan < sire.sire
