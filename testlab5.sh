#!/usr/bin/env bash

SCRIPT_PATH=$(cd `dirname $0` && pwd)
cd ${SCRIPT_PATH}

SBT_ARGS="testOnly Lab5Suite"
sbt "${SBT_ARGS}"
