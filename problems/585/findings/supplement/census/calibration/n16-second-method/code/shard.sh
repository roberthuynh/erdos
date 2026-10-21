#!/bin/bash
# One shard: plain (unpruned) stock geng -d5 -D5 <n> <res>/<mod> into a file, then the SAT decider.
# Usage: shard.sh <tag> <n> <res> <mod>
set -u
tag=$1; n=$2; r=$3; mod=$4
LANE="${ERDOS585_CENSUS_CALIBRATION_N16_SECOND_METHOD_CODE_SHARD_SH_LANE:?Set ERDOS585_CENSUS_CALIBRATION_N16_SECOND_METHOD_CODE_SHARD_SH_LANE to the original LANE dependency; see REPRODUCTION-BOUNDARY.md}"
SP="${ERDOS585_SCRATCH_DIR:?Set ERDOS585_SCRATCH_DIR to a writable scratch directory}"
GENG="${ERDOS585_CENSUS_CALIBRATION_N16_SECOND_METHOD_CODE_SHARD_SH_GENG:?Set ERDOS585_CENSUS_CALIBRATION_N16_SECOND_METHOD_CODE_SHARD_SH_GENG to the original GENG dependency; see REPRODUCTION-BOUNDARY.md}"
PY="${ERDOS585_CENSUS_CALIBRATION_N16_SECOND_METHOD_CODE_SHARD_SH_PY:?Set ERDOS585_CENSUS_CALIBRATION_N16_SECOND_METHOD_CODE_SHARD_SH_PY to the original PY dependency; see REPRODUCTION-BOUNDARY.md}"
mkdir -p "$SP" "$LANE/logs/$tag"
base="$LANE/logs/$tag/n${n}_r${r}_m${mod}"
g6="$SP/${tag}_n${n}_r${r}_m${mod}.g6"
[ -e "$base.done" ] && exit 0
t0=$(date +%s)
"$GENG" -d5 -D5 "$n" "$r/$mod" > "$g6" 2> "$base.geng.err"
gst=$?
t1=$(date +%s)
"$PY" "$LANE/code/pairsat.py" "$g6" "$base" --solver m22 --n "$n" --deg 5 --log "$base.progress" --every 50000 > "$base.out" 2> "$base.err"
pst=$?
t2=$(date +%s)
lines=$(wc -l < "$g6" | tr -d ' ')
sha=$(shasum -a 256 "$g6" | cut -d' ' -f1)
echo "tag=$tag n=$n res=$r mod=$mod geng_status=$gst decider_status=$pst g6_lines=$lines g6_sha256=$sha geng_s=$((t1-t0)) decide_s=$((t2-t1))" > "$base.meta"
if [ "$gst" -eq 0 ] && [ "$pst" -eq 0 ] && grep -q '^>Z' "$base.geng.err"; then touch "$base.done"; fi
