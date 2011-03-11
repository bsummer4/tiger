#!/bin/sh -e

[ 0 -ne $# ]
prog=$1
shift

if [ 0 = $# ]
then while read x; do echo $x | $prog; done
else echo "$*" | $prog
fi
