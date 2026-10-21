#!/bin/bash
# Rerun the T1 census (author's list data/t1_Y.txt, 76,975 marked graphs) with the independent rpair.
cd "$(dirname "$0")/t1census" || exit 1
awk '{ print > sprintf("part_%02d", (NR - 1) % 16) }' ../../../data/t1_Y.txt
for f in part_??; do
  ( timeout 240 ../rpair t < "$f" > "$f.out"; echo "$f exit=$?" >> status.txt ) &
done
wait
echo DONE >> status.txt
