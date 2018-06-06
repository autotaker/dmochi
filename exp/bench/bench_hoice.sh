#!/bin/bash

PROJECT_DIR=../..
SRC_DIR=$PROJECT_DIR/benchmarks/clauses/lia/mochi
TESTS=`cat testcases`

if [ $# -gt 0 ]; then
    TESTS="$@"
fi

HOICE=hoice

TIMEOUT=100
TIMEOUT_CMD=timeout
TIME=/usr/bin/time

LOG_DIR=log/hoice_smt


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
    src=$testcase.smt2
    cp $SRC_DIR/$src work/$src
    $TIME -o $LOG_DIR/$testcase.time $TIMEOUT_CMD $TIMEOUT $HOICE work/$src > $LOG_DIR/$testcase.log 
done
