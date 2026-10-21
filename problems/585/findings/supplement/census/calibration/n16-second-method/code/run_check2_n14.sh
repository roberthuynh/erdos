#!/bin/bash
# Check 2 at n = 14: 40 shards of plain geng -d5 -D5 14, 4 workers.
LANE="${ERDOS585_CENSUS_CALIBRATION_N16_SECOND_METHOD_CODE_RUN_CHECK2_N14_SH_LANE:?Set ERDOS585_CENSUS_CALIBRATION_N16_SECOND_METHOD_CODE_RUN_CHECK2_N14_SH_LANE to the original LANE dependency; see REPRODUCTION-BOUNDARY.md}"
echo "start $(date '+%F %T')"
seq 0 39 | xargs -P 4 -I{} /bin/bash "$LANE/code/shard.sh" check2 14 {} 40
echo "end $(date '+%F %T')"
