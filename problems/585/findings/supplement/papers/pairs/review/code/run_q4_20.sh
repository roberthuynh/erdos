#!/bin/bash
# geng (independent of genbg) + own hd tester, connected bipartite quartic graphs on 20 vertices, 16 shards.
cd "$(dirname "$0")/q4_20" || exit 1
G=~/.cache/erdos585/nauty2_9_3/geng
for i in $(seq 0 15); do
  ( timeout 240 "$G" -q -c -b -d4 -D4 20 "$i/16" > "g_$i.g6"; echo "$i geng_exit=$?" >> status.txt ) &
done
wait
for i in $(seq 0 15); do
  ( timeout 240 ../hd < "g_$i.g6" > "hd_$i.out"; echo "$i hd_exit=$?" >> status.txt ) &
done
wait
echo DONE >> status.txt
