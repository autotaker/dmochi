#!/bin/bash

PROJECT_DIR=../..
TESTS=`cat testcases`

if [ $# -gt 0 ]; then
    TESTS="$@"
fi

DMOCHI=dmochi

TIMEOUT=100
TIMEOUT_CMD=timeout

LOG_DIR=log/dmochi_prog


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
    testname=${testcase%.prog}
    basename=$(basename $testcase).prog
    cp $PROJECT_DIR/sample/mochi/$testname.prog work/$basename
    DMOCHI_FLAG="--hccs gch --incremental"
    $TIMEOUT_CMD $TIMEOUT $DMOCHI $DMOCHI_FLAG work/$basename > $LOG_DIR/$testname.log
    cp work/$basename.result.json $LOG_DIR/$testname.result.json
done
