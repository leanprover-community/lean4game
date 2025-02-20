#!/usr/bin/env bash
cores=$(nproc --all)
cpu_measure=$(top -bn2 | grep '%Cpu' | tail -1)
mem_measure=$(top -bn2 | grep 'Mem' | head -1)

cpu=$(echo $cpu_measure | awk -v cores=$cores '{print 1-($8/(cores*100))}')
mem=$(echo $mem_measure | awk '{print $8/$4}') 

printf "CPU, MEM\n%.2f, %.2f\n" $cpu $mem 



