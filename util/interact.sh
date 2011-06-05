#!/bin/sh -e

[ 0 -ne $# ]
prog=$1
shift

if [ 0 = $# ]
then while x=$(line); do echo "$x" | $prog || true; done
else echo "$*" | $prog
fi
