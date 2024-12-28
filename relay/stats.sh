#!/usr/bin/env bash

# Load python interpreter
python=/usr/bin/python3
# Load python script
cpu_usage=$L4G_DIR/lean4game/relay/cpu_usage.py
# Execute python script
cpu=$($python $cpu_usage)
# Calculate memory usage by computing used_memory/total_memory
mem=$(free | sed '2q;d' | awk '{print $3/$2}')

printf "CPU, MEM\n%.2f, %.2f\n" $cpu $mem
