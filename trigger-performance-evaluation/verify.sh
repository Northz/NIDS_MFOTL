#!/bin/bash

EXPERIMENTS=$1
ITERATIONS=10

echo "Verifying experiments.."

for experiment in $( seq 1 $EXPERIMENTS ); do
	./verify.sh $experiment
done

echo "Done."