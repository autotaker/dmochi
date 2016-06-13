#!/bin/bash
TESTS="sum.txt"

for bool in `find log -name "*.bool.log"`
do
    bool=${bool%.log}
    SIZE="`grep 'Boolean Program Size' $bool.log | sed -e 's/[^:]*: *//'`"
    RESULT="`grep 'extracting a counterexample' $bool.log > /dev/null && echo 'Unsafe' || echo 'Safe'`"
    TIME_BOOL="`grep 'Elapsed Time:' $bool.typed.log | sed -e 's/[^:]*: \([0-9.]*\) sec/\1/'`"
    TIME_HORSAT="`grep 'Elapsed Time:' $bool.horsat.log | sed -e 's/[^:]*: \([0-9.]*\)sec/\1/'`"
    TIME_HORSAT2="`grep 'Elapsed Time:' $bool.horsat2.log | sed -e 's/[^:]*: \([0-9.]*\)sec/\1/'`"
    TIME_PREFACE="`grep 'Total:' $bool.preface.log | sed -e 's/[^:]*: \([0-9]*\)ms/\1/'`"
    TIME_PREFACE=`echo 'scale=3;' $TIME_PREFACE.0/1000.0 | bc`
    echo "${bool#log/},$SIZE,$RESULT,$TIME_BOOL,$TIME_HORSAT,$TIME_HORSAT2,$TIME_PREFACE"
#    echo '\t' untyped `tail -n 1 $bool.log`
#    echo '\t' typed   `tail -n 1 $bool.typed.log`
#    echo '\t' horsat  `tail -n 1 $bool.horsat.log`
#    echo '\t' horsat2 `grep 'Elapsed Time:' $bool.horsat2.log`
#    echo '\t' preface `grep 'Total:' $bool.preface.log`
#    echo '\t' untyped ans: `grep 'extracting a counterexample' $bool.log > /dev/null && echo 'Unsafe' || echo 'Safe'`
#    echo '\t' typed ans: `grep   'extracting a counterexample' $bool.typed.log > /dev/null && echo 'Unsafe' || echo 'Safe'`
#    echo '\t' horsat ans: `grep 'The property is' $bool.horsat.log`
#    echo '\t' horsat2 ans: `grep 'The property is' $bool.horsat2.log`
#    echo '\t' preface ans: `grep 'Decision' $bool.preface.log`
done
