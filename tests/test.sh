#!/bin/bash

TESTS="sum sum-acc mc91 copy fold isnil reverse fold_left fold_right fold_div fold_fun_list zip"

if [ $# -gt 0 ]; then
    TESTS="$@"
fi

DMOCHI=dmochi

TIMEOUT=200
TIMEOUT_CMD=timeout

if [ ! -e work ]; then
    mkdir work
fi

if [ ! -e log ]; then
    mkdir log
fi

set -x

if [ ! -v DMOCHI_FLAG ]; then
    DMOCHI_FLAG="--hccs gch --context-sensitive"
fi

for testcase in $TESTS
do
    echo "Running testcase" $testcase
    rm -f work/$testcase*
    basename=$(basename $testcase.prog)
    cp ../sample/$testcase.prog work/$basename
    $TIMEOUT_CMD $TIMEOUT $DMOCHI $DMOCHI_FLAG work/$basename > log/$basename.log || exit 1
done
