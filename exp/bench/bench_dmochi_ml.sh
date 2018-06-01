#!/bin/bash

PROJECT_DIR=../..
SRC_DIR=$PROJECT_DIR/benchmarks/caml/lia/mochi
TESTS=`cat testcases`

if [ $# -gt 0 ]; then
    TESTS="$@"
fi

DMOCHI=dmochi

TIMEOUT=100
TIMEOUT_CMD=timeout

LOG_DIR=log/dmochi_ml_hoice_no_embed


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
    cp $SRC_DIR/$src work/$src
    DMOCHI_FLAG="--cegar abst --no-embed-cur-cond --hccs hoice"
    $TIMEOUT_CMD $TIMEOUT $DMOCHI $DMOCHI_FLAG work/$src > $LOG_DIR/$testcase.log
    cp work/$src.result.json $LOG_DIR/$testcase.result.json
done
