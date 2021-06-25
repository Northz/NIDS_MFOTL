#!/bin/bash
cd "./experiments/experiment-$1"

TIMEFORMAT='%3R;%3U;%3S'

time_rewritten=$(time (../../../monpoly -formula ./formula.txt -no_trigger -log ./log.txt -sig ./signature.txt -no_rw -verified > ./out-rewritten.txt) 2>&1)
# rewritten_loop_time=$(cat ./out-rewritten.txt | grep loop | sed "s/loop: //" | awk '{n += $1}; END{print n}')
rewritten_meval_time=$(cat ./out-rewritten.txt | grep meval | sed "s/meval: //" | awk '{n += $1}; END{print n}')

time_native=$(time (../../../monpoly -formula ./formula.txt -log ./log.txt -sig ./signature.txt -no_rw -verified  > ./out-native.txt) 2>&1)
trigger_time=$(cat ./out-native.txt | grep mmtaux | sed "s/mmtaux: //" | awk '{n += $1}; END{print n}')
# native_loop_time=$(cat ./out-native.txt | grep loop | sed "s/loop: //" | awk '{n += $1}; END{print n}')
native_meval_time=$(cat ./out-native.txt | grep meval | sed "s/meval: //" | awk '{n += $1}; END{print n}')

# even though we simply discard out-rewritten, it's more comparable this way
rm ./out-rewritten.txt
rm ./out-native.txt

echo "$1;$time_rewritten;$rewritten_meval_time;$time_native;$trigger_time;$native_meval_time"
