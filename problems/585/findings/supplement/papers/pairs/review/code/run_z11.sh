#!/bin/bash
# Independent Z census at n = 11: geng -d3 -D6 11 28:28 (min degree 3 is forced, given W1 at n = 10,
# checked below), 400 shards, pair-free ones by rpair. Expected (author): 5,122.
cd "$(dirname "$0")/z11" || exit 1
G=~/.cache/erdos585/nauty2_9_3/geng
seq 0 399 | xargs -P 16 -I{} /bin/bash -c "timeout 240 $G -q -d3 -D6 11 28:28 {}/400 | timeout 240 ../rpair f | grep FREE > free_{}.txt; echo {} \${PIPESTATUS[0]} \${PIPESTATUS[1]} >> status.txt"
# W1 at n = 10 for e = 26..28, Delta <= 6 (no pair-free graph expected)
timeout 240 $G -q -D6 10 26:28 | timeout 240 ../rpair f > w1_n10.out
echo "w1_n10 exit=$?" >> status.txt
echo DONE >> status.txt
