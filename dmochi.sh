#!/bin/bash
dir=$(dirname $(readlink $0 || echo $0))
bin=$dir/bin
lib=$dir/lib
exec /lib64/ld-linux-x86-64.so.2 --library-path $lib $bin/dmochi "$@"
