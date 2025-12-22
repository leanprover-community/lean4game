#!/usr/bin/env bash

# Load python interpreter
python=/usr/bin/python3
# Load python script
cpu_usage=$CPU_SCRIPT
# Execute python script
cpu=$($python $cpu_usage)
# Calculate memory usage by computing (used memory - cached/buffer memory) divided by total memory
# We can consider cached/buffer memory to be free.
# As cached/buffer memory can be greater than the currently used memory we also use its absolute value.
mem=$(free | sed '2q;d' | awk '{print sqrt(($3-$6)^2)/$2}')

printf "CPU, MEM\n%f, %f\n" $cpu $mem
