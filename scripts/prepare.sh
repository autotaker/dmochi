#!/bin/bash

set -xe
distname=$(lsb_release -i -s)
z3url='https://github.com/Z3Prover/z3/releases/download/z3-4.6.0/'
if [ $distname = "Ubuntu" -o $distname = "LinuxMint" ]; then
    z3dir='z3-4.6.0-x64-ubuntu-16.04'
    z3url=$z3url$z3dir.zip
elif [ $distname = "Debian" ]; then
    z3dir='z3-4.6.0-x64-debian-8.10'
    z3url=$z3url$z3dir.zip
else
    z3url='https://github.com/Z3Prover/z3/archive/z3-4.6.0.zip'
    z3dir='z3-z3-4.6.0'
fi
if [ ! -e z3-4.6.0.zip ]; then
    curl -L "$z3url" > z3-4.6.0.zip
    unzip z3-4.6.0.zip
    mv $z3dir 'z3-4.6.0'
    if [ -e z3-4.6.0/configure ]; then
        # from source
        prefix=$(pwd)/z3-4.6.0
        (cd z3-4.6.0; ./configure --prefix=$prefix; make -j$(nproc) -C build install)
    else
        mkdir z3-4.6.0/lib
        mv z3-4.6.0/bin/libz3.so z3-4.6.0/lib/
    fi
fi
