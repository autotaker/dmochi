#!/bin/sh

set -xe
distname=$(lsb_release -i -s)
z3url='https://github.com/Z3Prover/z3/releases/download/z3-4.6.0/'
if [ $distname = "Ubuntu" -o $distname = "LinuxMint" ]; then
    z3dir='z3-4.6.0-x64-ubuntu-16.04'
elif [ $distname = "Debian" ]; then
    z3dir='z3-4.6.0-x64-debian-8.10'
else
    z3dir='z3-4.6.0'
fi
if [ ! -e z3-4.6.0.zip ]; then
    z3url=${z3url}${z3dir}.zip
    curl -L "$z3url" > z3-4.6.0.zip
    unzip z3-4.6.0.zip
    mv $z3dir 'z3-4.6.0'
    mkdir z3-4.6.0/lib
    mv z3-4.6.0/bin/libz3.so z3-4.6.0/lib/
fi
