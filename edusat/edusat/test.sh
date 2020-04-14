#!/bin/bash

FILES1=./test-cases/Group1/unsat/*.cnf
FILES2=./test-cases/Group1/sat/*.cnf
for f in $FILES1
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done
for f in $FILES2
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done



FILES1=./test-cases/Group2/unsat/*.cnf
FILES2=./test-cases/Group2/sat/*.cnf
for f in $FILES1
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done
for f in $FILES2
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done



FILES1=./test-cases/Group3/unsat/*.cnf
FILES2=./test-cases/Group3/sat/*.cnf
for f in $FILES1
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done
for f in $FILES2
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done




FILES1=./test-cases/Group4/unsat/*.cnf
FILES2=./test-cases/Group4/sat/*.cnf
for f in $FILES1
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done
for f in $FILES2
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done




FILES1=./test-cases/Group5/unsat/*.cnf
FILES2=./test-cases/Group5/sat/*.cnf
for f in $FILES1
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done
for f in $FILES2
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done



FILES1=./test-cases/Group6/unsat/*.cnf
FILES2=./test-cases/Group6/sat/*.cnf
for f in $FILES1
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done
for f in $FILES2
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done



FILES1=./test-cases/Group7/unsat/*.cnf
FILES2=./test-cases/Group7/sat/*.cnf
for f in $FILES1
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done
for f in $FILES2
do
  echo "Processing $f file..."
  REDUCEDB=0 ./edusat -vardh 0 $f
  REDUCEDB=1 ./edusat -vardh 0 $f
  REDUCEDB=0 ./edusat -vardh 2 $f
  REDUCEDB=1 ./edusat -vardh 2 $f
done



# FILES1=./test-cases/Group8/unsat/*.cnf
# FILES2=./test-cases/Group8/sat/*.cnf
# for f in $FILES1
# do
#   echo "Processing $f file..."
#   REDUCEDB=0 ./edusat -vardh 0 $f
#   REDUCEDB=1 ./edusat -vardh 0 $f
#   REDUCEDB=0 ./edusat -vardh 2 $f
#   REDUCEDB=1 ./edusat -vardh 2 $f
# done
# for f in $FILES2
# do
#   echo "Processing $f file..."
#   REDUCEDB=0 ./edusat -vardh 0 $f
#   REDUCEDB=1 ./edusat -vardh 0 $f
#   REDUCEDB=0 ./edusat -vardh 2 $f
#   REDUCEDB=1 ./edusat -vardh 2 $f
# done


# FILES1=./test/sat/*.cnf
# FILES2=./test/unsat/*.cnf
# FILES3=./test/comp17/*.cnf

# for f in $FILES1
# do
#   echo "Processing $f file..."
#   # take action on each file. $f store current file name
#   # cat $f
#   REDUCEDB=0 ./edusat $f
#   # REDUCEDB=0 ./edusat $f
#   REDUCEDB=1 ./edusat $f
#   # REDUCEDB=1 ./edusat $f
# done

# for f in $FILES2
# do
#   echo "Processing $f file..."
#   # take action on each file. $f store current file name
#   # cat $f
#   # REDUCEDB=0 ./edusat $f
#   REDUCEDB=0 ./edusat $f
#   # REDUCEDB=1 ./edusat $f
#   REDUCEDB=1 ./edusat $f

# done

# # for f in $FILES3
# # do
# #   echo "Processing $f file..."
# #   # take action on each file. $f store current file name
# #   # cat $f
# #   ./edusat f
# # done