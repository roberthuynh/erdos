#!/bin/bash
# Rerun the T2 census (author's X list, 66,992 graphs X = Z + v) with the independent rpair, mode r.
cd "$(dirname "$0")/t2census" || exit 1
awk '{ print > sprintf("part_%02d", (NR - 1) % 16) }' ../t2_Xv.txt
for f in part_??; do
  ( timeout 240 ../rpair r < "$f" > "$f.out"; echo "$f exit=$?" >> status.txt ) &
done
wait
echo DONE >> status.txt
