#!/bin/bash

TOHORS="../../Boolean/ToHORS"
MODELCHECK="../../ML/Test"
SRCDIR="./src/"
BOOLDIR="./bool/"
HORSDIR="./hors/"
LOGDIR="./log/"


HORSAT="../../../horsat-1.01/horsat"
HORSAT2="../../../horsat2-0.92/horsat2"
PREFACE="preface"

TESTS="copy.txt      \
fold_div.txt         \
fold_fun_list.txt    \
fold_left.txt        \
for_all_eq_pair.txt  \
isnil.txt  \
length.txt \
reverse.txt \
search.txt \
sum.txt \
zip.txt"

#TESTS="reverse.txt"

for test in $TESTS
do
#  $MODELCHECK $SRCDIR$test > $LOGDIR$test.log
  mv $SRCDIR$test.bool $BOOLDIR
#  $TOHORS $BOOLDIR$test.bool
#  mv $BOOLDIR$test.bool.naive.hrs $HORSDIR
#  mv $BOOLDIR$test.bool.selective.horsat.hrs $HORSDIR
#  mv $BOOLDIR$test.bool.selective.preface.hrs $HORSDIR
#  mv $BOOLDIR$test.bool.selective.church.hrs $HORSDIR
  gtimeout 100 hiboch $BOOLDIR$test.bool | tee $LOGDIR$test.bool.log
  gtimeout 100 hiboch -t $BOOLDIR$test.bool | tee $LOGDIR$test.bool.typed.log
  
  #gtimeout 200 $HORSAT $HORSDIR$test.bool.naive.hrs  | tee $LOGDIR$test.naive.horsat.log
  #gtimeout 200 $PREFACE $HORSDIR$test.bool.naive.hrs | tee $LOGDIR$test.naive.preface.log

#  gtimeout 200 $HORSAT $HORSDIR$test.bool.selective.horsat.hrs | tee $LOGDIR$test.selective.horsat.log
#  gtimeout 200 $PREFACE $HORSDIR$test.bool.selective.preface.hrs | tee $LOGDIR$test.selective.preface.log
#  
#  gtimeout 200 $HORSAT $HORSDIR$test.bool.selective.church.hrs | tee $LOGDIR$test.selective.church.horsat.log
#  gtimeout 200 $PREFACE $HORSDIR$test.bool.selective.church.hrs | tee $LOGDIR$test.selective.church.preface.log
  gtimeout 200 $HORSAT2 $HORSDIR$test.bool.selective.horsat.hrs | tee $LOGDIR$test.selective.horsat2.log
  gtimeout 200 $HORSAT2 $HORSDIR$test.bool.selective.church.hrs | tee $LOGDIR$test.selective.church.horsat2.log
done

