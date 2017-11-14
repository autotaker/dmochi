#!/bin/bash

PROJECT_DIR=../..
TESTS=`cat testcases`

if [ $# -gt 0 ]; then
    TESTS="$@"
fi

DMOCHI=dmochi

TIMEOUT=100
TIMEOUT_CMD=timeout

LOG_DIR=log/dmochi_ml


if [ ! -e work ]; then
    mkdir work
fi

if [ ! -e $LOG_DIR ]; then
    mkdir -p $LOG_DIR
fi

set -x

if [ ! -v DMOCHI_FLAG ]; then
    DMOCHI_FLAG="--hccs gch --context-sensitive"
fi

for testcase in $TESTS
do
    echo "Running testcase" $testcase
    rm -f work/$testcase*
    src=$testcase.ml
    cp $PROJECT_DIR/sample/mochi/$src work/$src
    DMOCHI_FLAG="--hccs gch --incremental"
    $TIMEOUT_CMD $TIMEOUT $DMOCHI $DMOCHI_FLAG work/$src > $LOG_DIR/$testcase.log
    cp work/$src.result.json $LOG_DIR/$testcase.result.json
done