#!/bin/sh
while read x; do echo $x | $1; done
