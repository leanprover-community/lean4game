#!/usr/bin/env bash

# Load python interpreter
python=/usr/bin/python3
# Load python script
cpu_usage=$CPU_SCRIPT
# Execute python script
cpu=$($python $cpu_usage)
# Calculate memory usage by computing 1 - %free_memory
mem=$(free | sed '2q;d' | awk '{print 1 - ($4/$2)}')

printf "CPU, MEM\n%f, %f\n" $cpu $mem
