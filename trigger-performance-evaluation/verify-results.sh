#!/bin/bash

echo "Checking for experiments where different results were obtained.."

for dir in ./experiments/*/
do
    dir=${dir%*/}
    experiment="${dir##*/}"
	file="./experiments/$experiment/check.txt"
	if [ -f "$file" ]; then
	    cat "$file"
	fi
done

printf "\n"
echo "Done."