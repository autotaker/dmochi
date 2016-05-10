#!/bin/bash


TEST1="example1.txt example2.txt example3.txt example4.txt example5.txt example6.txt example7.txt example9.txt"
TEST2="ack.txt copy-1.txt isnil.txt sum.txt fold.txt mc91.txt reverse.txt"
TEST3="length.txt sum-e.txt copy.txt fold_div.txt fold_fun_list.txt fold_left.txt for_all_eq_pair.txt search.txt zip.txt"
TESTS="$TEST1 $TEST2 $TEST3"

DMOCHI=../dist/build/dmochi/dmochi
HIBOCH=../dist/build/hiboch/hiboch
TOHORS=../dist/build/tohors/tohors

HORSAT=../../horsat-1.01/horsat
HORSAT2=../../horsat2-0.92/horsat2

if [ ! -e work ]; then
    mkdir work
fi

if [ ! -e log ]; then
    mkdir log
fi

set -e

for testcase in $TEST2
do
    echo "Running testcase" $testcase
    rm -f work/$testcase*
    cp ../sample/$testcase work/$testcase
    $DMOCHI work/$testcase > log/$testcase.log
    for bool in work/$testcase*.bool
    do
        bool=${bool#work/}
        echo $bool
        $TOHORS work/$bool
        $HIBOCH work/$bool > log/$bool.log
        $HORSAT  work/$bool.selective.horsat.hrs > log/$bool.horsat.log
        $HORSAT2 work/$bool.selective.horsat.hrs > log/$bool.horsat2.log
    done
done


