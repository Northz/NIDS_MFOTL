#!/bin/bash
cd "./asymptotic-experiments/$1"

TIMEFORMAT='%3R;%3U;%3S'

if [ ! -f ./formula-$2.txt ]; then
	exit 0
fi

time_native=$(time (../../../monpoly -formula ./formula-$2.txt -log ./log-$2.txt -sig ./signature.txt -no_rw -verified  > ./out-native.txt) 2>&1)
trigger_time=$(cat ./out-native.txt | grep mmtaux | sed "s/mmtaux: //" | awk '{n += $1}; END{print n}')
native_meval_time=$(cat ./out-native.txt | grep meval | sed "s/meval: //" | awk '{n += $1}; END{print n}')

rm ./out-native.txt

echo "$1;$2;$time_native;$trigger_time;$native_meval_time"
