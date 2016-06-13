#!/bin/bash


TEST2="ack.txt copy-1.txt isnil.txt sum.txt fold.txt mc91.txt reverse.txt"
TEST3="length.txt sum-e.txt copy.txt fold_div.txt fold_fun_list.txt fold_left.txt zip.txt"
TESTS="$TEST2 $TEST3"

if [ $# -gt 0 ]; then
    TESTS="$@"
fi

DMOCHI=dmochi
HIBOCH=hiboch
TOHORS=tohors

HORSAT=../../../../horsat-1.01/horsat
HORSAT2=../../../../horsat2-0.92/horsat2
PREFACE=preface
SAMPLE=../../../sample

TIMEOUT=200

if [ ! -e work ]; then
    mkdir work
fi

if [ ! -e log ]; then
    mkdir log
fi

set -x

for testcase in $TESTS
do
    echo "Running testcase" $testcase
    rm -f work/$testcase*
    cp $SAMPLE/$testcase work/$testcase
    gtimeout $TIMEOUT $DMOCHI work/$testcase > log/$testcase.log
    for bool in `find work -name "$testcase*.bool"`
    do
        bool=${bool#work/}
        echo $bool
        $TOHORS work/$bool > /dev/null
        gtimeout $TIMEOUT $HIBOCH work/$bool > log/$bool.log
        gtimeout $TIMEOUT $HIBOCH -t work/$bool > log/$bool.typed.log
        gtimeout $TIMEOUT $HORSAT  work/$bool.selective.horsat.hrs > log/$bool.horsat.log
        gtimeout $TIMEOUT $HORSAT2 work/$bool.selective.horsat.hrs > log/$bool.horsat2.log
        gtimeout $TIMEOUT $PREFACE work/$bool.selective.preface.hrs > log/$bool.preface.log
    done
done
