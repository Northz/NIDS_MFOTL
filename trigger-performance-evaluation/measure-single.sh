#!/bin/bash
cd "./experiments/experiment-$1"

TIMEFORMAT='%3R;%3U;%3S'

time_rewritten=$(time (../../../monpoly -formula ./formula-rewritten.txt -log ./log.txt -sig ./signature.txt -no_rw -verified > /dev/null) 2>&1)

time_native=$(time (../../../monpoly -formula ./formula-native.txt -log ./log.txt -sig ./signature.txt -no_rw -verified  > /dev/null) 2>&1)

echo "$1;$time_rewritten;$time_native"
