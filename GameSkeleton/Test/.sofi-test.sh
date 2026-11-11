#!/bin/bash

# version [2025-03-14]

# This is just a short auxiliary script to that tests very basic functionality
# of sofi.sh.  It should be used in conjunction with the folder
# .sofi-test-folders

time="$(date +"%Y-%m-%d--%H-%M-%S")"
testdir=".sofi-test_${time}"
cp -r ./.sofi-test-folders ./$testdir
echo -e "\nTEST1: Running sofi.sh without a parameter should result in an error."
./sofi.sh
echo -e "\nTEST2: Running sofi.sh with a folder as parameter that does not have an accompanying .lean file should result in an error."
./sofi.sh "./${testdir}/BadTest"
echo -e "\nTEST3: Running sofi.sh with a file as parameter should result in an error."
./sofi.sh "./${testdir}/Test.lean"
echo -e "\nTEST4 (Correct usage of sofi.sh):"
./sofi.sh "./${testdir}/Test"
