#!/bin/bash
FILES1=./test/sat/*.cnf
FILES2=./test/unsat/*.cnf
FILES3=./test/comp17/*.cnf

for f in $FILES1
do
  echo "Processing $f file..."
  # take action on each file. $f store current file name
  # cat $f
  ./edusat -vardh 0 $f
  ./edusat $f
done

for f in $FILES2
do
  echo "Processing $f file..."
  # take action on each file. $f store current file name
  # cat $f
  ./edusat -vardh 0 $f
  ./edusat $f
done

# for f in $FILES3
# do
#   echo "Processing $f file..."
#   # take action on each file. $f store current file name
#   # cat $f
#   ./edusat f
# done