#!/bin/bash

TOHORS="tohors"
MC="hiboch"
SRCDIR="./src/"
HORSDIR="./hors/"
LOGDIR="./log/"
TMPDIR="./tmp/"

HORSAT="../../../../horsat-1.01/horsat"
HORSAT2="../../../../horsat2-0.92/horsat2"
PREFACE="preface"

TESTS="\
flow1.bool \
flow2.bool \
flow3.bool \
flow4.bool \
flow5.bool \
flow6.bool \
flow7.bool \
flow8.bool \
flow9.bool \
flow10.bool \
flow11.bool \
flow12.bool"
#TESTS="\
#flow8.bool \
#flow9.bool \
#flow1.bool \
#flow10.bool \
#flow11.bool \
#flow12.bool"
#TESTS="\
#flow13.bool \
#flow14.bool \
#flow15.bool \
#flow16.bool \
#flow17.bool"

#TESTS="flow2.bool"
mkdir -p $HORSDIR
mkdir -p $LOGDIR
mkdir -p $TMPDIR
set -x

for test in $TESTS
do
  cp $SRCDIR$test $TMPDIR
  $TOHORS $TMPDIR$test > /dev/null
  mv $TMPDIR$test.naive.hrs $HORSDIR
  mv $TMPDIR$test.selective.horsat.hrs $HORSDIR
  mv $TMPDIR$test.selective.preface.hrs $HORSDIR
  mv $TMPDIR$test.selective.church.hrs $HORSDIR

#  gtimeout 200 $HORSAT $HORSDIR$test.naive.hrs  | tee $LOGDIR$test.naive.horsat.log
#  gtimeout 200 $PREFACE $HORSDIR$test.naive.hrs | tee $LOGDIR$test.naive.preface.log

  # gtimeout 200 $HORSAT $HORSDIR$test.selective.church.hrs | tee $LOGDIR$test.selective.church.horsat.log
  # gtimeout 200 $PREFACE $HORSDIR$test.selective.church.hrs | tee $LOGDIR$test.selective.church.preface.log
  gtimeout 200 $MC -t $TMPDIR$test > $LOGDIR$test.log
  gtimeout 200 $HORSAT  $HORSDIR$test.selective.horsat.hrs  > $LOGDIR$test.selective.horsat.log
  gtimeout 200 $HORSAT2 $HORSDIR$test.selective.horsat.hrs  > $LOGDIR$test.selective.horsat2.log
  gtimeout 200 $PREFACE $HORSDIR$test.selective.preface.hrs > $LOGDIR$test.selective.preface.log
done

