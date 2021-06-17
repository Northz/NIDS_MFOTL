#!/bin/bash
cd "./experiments/experiment-$1"

../../../monpoly -formula ./formula-rewritten.txt -log ./log.txt -sig ./signature.txt -no_rw -verified > /dev/null

if (($? > 0)); then
	echo "Command '../../../monpoly -formula ./formula-rewritten.txt -log ./log.txt -sig ./signature.txt -no_rw -verified' failed!"
	echo "Check the written error.log"
	exit 1
fi

../../../monpoly -formula ./formula-native.txt -log ./log.txt -sig ./signature.txt -no_rw -verified > /dev/null

if (($? > 0)); then
	echo "Command '../../../monpoly -formula ./formula-native.txt -log ./log.txt -sig ./signature.txt -no_rw -verified' failed!"
	echo "Check the written error.log"
	exit 2
fi