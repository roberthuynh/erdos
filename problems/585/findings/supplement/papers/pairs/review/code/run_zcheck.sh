#!/bin/bash
# Independent Z census: all graphs on n = 7..10 vertices with e = 3n - 5 and max degree <= 6 (geng, no
# min-degree restriction), pair-free ones by rpair. Expected (author, via cores + degree-3 additions):
# 1, 4, 41, 457.
cd "$(dirname "$0")/zcheck" || exit 1
G=~/.cache/erdos585/nauty2_9_3/geng
for n in 7 8 9; do
  e=$((3 * n - 5))
  ( timeout 240 "$G" -q -D6 "$n" "$e:$e" | timeout 240 ../rpair f > "z_$n.out"; echo "n=$n exit=$?" >> status.txt ) &
done
for i in $(seq 0 13); do
  ( timeout 240 "$G" -q -D6 10 25:25 "$i/14" | timeout 240 ../rpair f > "z_10_$i.out"; echo "n=10 part $i exit=$?" >> status.txt ) &
done
wait
echo DONE >> status.txt
