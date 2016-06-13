#!/bin/bash
TESTS="sum.txt"

for bool in `find log -name "*.bool.log"`
do
    bool=${bool%.log}
    echo $bool
    echo '\t' `grep 'Boolean Program Size' $bool.log`
    echo '\t' untyped `tail -n 1 $bool.log`
    echo '\t' typed   `tail -n 1 $bool.typed.log`
    echo '\t' horsat  `tail -n 1 $bool.horsat.log`
    echo '\t' horsat2 `grep 'Elapsed Time:' $bool.horsat2.log`
    echo '\t' preface `grep 'Total:' $bool.preface.log`
    echo '\t' untyped ans: `grep 'extracting a counterexample' $bool.log > /dev/null && echo 'Unsafe' || echo 'Safe'`
    echo '\t' typed ans: `grep   'extracting a counterexample' $bool.typed.log > /dev/null && echo 'Unsafe' || echo 'Safe'`
    echo '\t' horsat ans: `grep 'The property is' $bool.horsat.log`
    echo '\t' horsat2 ans: `grep 'The property is' $bool.horsat2.log`
    echo '\t' preface ans: `grep 'Decision' $bool.preface.log`
done
