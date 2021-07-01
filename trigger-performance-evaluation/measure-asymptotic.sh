#!/bin/bash

ITERATIONS=10

echo "Running experiments.."

echo "experiment;asymptotic;native real time;native user time;native sys time;native trigger time;native meval time" > ./measurements-asymptotic.csv

for dir in ./asymptotic-experiments/*/
do
    dir=${dir%*/}            # remove the trailing "/"
    experiment="${dir##*/}"  # print everything after the final "/"
	
	echo "Running experiment $experiment for $ITERATIONS iterations"
	for iteration in $( seq 1 $ITERATIONS ); do
		./measure-single-asymptotic.sh $experiment baseline >> ./measurements-asymptotic.csv
		./measure-single-asymptotic.sh $experiment 2n >> ./measurements-asymptotic.csv
		./measure-single-asymptotic.sh $experiment 2l >> ./measurements-asymptotic.csv
		./measure-single-asymptotic.sh $experiment 4n >> ./measurements-asymptotic.csv
		./measure-single-asymptotic.sh $experiment 4l >> ./measurements-asymptotic.csv
		./measure-single-asymptotic.sh $experiment 8n >> ./measurements-asymptotic.csv
		./measure-single-asymptotic.sh $experiment 8l >> ./measurements-asymptotic.csv
		./measure-single-asymptotic.sh $experiment 16n >> ./measurements-asymptotic.csv
		./measure-single-asymptotic.sh $experiment 16l >> ./measurements-asymptotic.csv
	done
done

echo "Done."