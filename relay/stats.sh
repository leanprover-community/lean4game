#!/bin/bash

# first argument is the process ID
pid="$1"

# number of CPUs available
nproc=$(nproc --all)

# hacky way to print the content of a CSV file containing CPU/Mem usage of the process
top -bn2 -p $pid | awk -v nproc=$nproc 'NR > 16 {$12=substr($0,72); printf "CPU, MEM\n%.2f, %.2f\n", $9/nproc, $10}'
