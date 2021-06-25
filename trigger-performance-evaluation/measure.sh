#!/bin/bash

START=$1
END=$2
ITERATIONS=10

echo "Running experiments.."

echo "experiment;rewritten real time;rewritten user time;rewritten sys time;rewritten meval time;native real time;native user time;native sys time;native trigger time;native meval time" > ./measurements.csv

for experiment in $( seq $START $END ); do
	echo "Running experiment #$experiment for $ITERATIONS iterations"
	for iteration in $( seq 1 $ITERATIONS ); do
		./measure-single.sh $experiment >> ./measurements.csv
	done
done

echo "Done."