#! /usr/bin/env bash

# usage: compare.sh <inputfilename>

time_command="/usr/bin/time"

echo "Number of bytes:"
$time_command wc -c $1

echo
echo "# Haskell version"
cd hs-checksum
$time_command stack exec hs-checksum-exe < ../$1
cd ..

echo
echo "C version"
$time_command c_checksum/c_checksum < $1

echo
echo "# Python version"
$time_command python3 py_checksum/py_checksum.py < $1


