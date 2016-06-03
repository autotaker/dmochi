#!/bin/bash

TOHORS="../../Boolean/ToHORS"
SRCDIR="./src/"
HORSDIR="./hors/"
LOGDIR="./log/"

HORSAT="../../../horsat-1.01/horsat"
PREFACE="preface"

TESTS="copy.txt.bool      \
fold_div.txt.bool         \
fold_fun_list.txt.bool    \
fold_left.txt.bool        \
for_all_eq_pair.txt.bool  \
isnil.txt.bool            \
length.txt.bool           \
reverse.txt.bool          \
search.txt.bool           \
sum.txt.bool              \
zip.txt.bool"



for test in $TESTS
do
  $TOHORS $SRCDIR$test
  mv $SRCDIR$test.naive.hrs $HORSDIR
  mv $SRCDIR$test.selective.horsat.hrs $HORSDIR
  mv $SRCDIR$test.selective.preface.hrs $HORSDIR
  mv $SRCDIR$test.selective.church.hrs $HORSDIR
done

# for test in $TESTS
# do
#   gtimeout 200 $HORSAT $HORSDIR$test.naive.hrs  | tee $LOGDIR$test.naive.horsat.log
#   gtimeout 200 $PREFACE $HORSDIR$test.naive.hrs | tee $LOGDIR$test.naive.preface.log
# 
#   gtimeout 200 $HORSAT $HORSDIR$test.selective.horsat.hrs | tee $LOGDIR$test.selective.horsat.log
#   gtimeout 200 $PREFACE $HORSDIR$test.selective.preface.hrs | tee $LOGDIR$test.selective.preface.log
#   
#   gtimeout 200 $HORSAT $HORSDIR$test.selective.church.hrs | tee $LOGDIR$test.selective.church.horsat.log
#   gtimeout 200 $PREFACE $HORSDIR$test.selective.church.hrs | tee $LOGDIR$test.selective.church.preface.log
# done

