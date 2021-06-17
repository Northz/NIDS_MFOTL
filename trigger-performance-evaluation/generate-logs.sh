#!/bin/bash

START=$1
END=$2

echo "Generating logs.."

for experiment in $( seq $START $END ); do
	echo "Generating log for experiment #$experiment"
	python log-generator.py --output-dir ./experiments/experiment-$experiment --signature ./experiments/experiment-$experiment/signature.txt
done

echo "Done."