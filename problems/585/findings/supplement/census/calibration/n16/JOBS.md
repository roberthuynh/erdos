# Historical reg5n16 configuration

Recorded 2026-10-06. Question: is there a 5-regular pair-free graph on 16 vertices?

The 03:48 run used 16 workers and `geng_pp -d5 -D5 16 r/20000`. Completed shards were recorded by `.done` markers.

- Binary: `code/geng_pp`, SHA-256 `c8b8ee91...c45b5a789` (full hashes in `logs/driver.log` and
  `logs/build.txt`). Source `code/pairprune.c` SHA-256 `66347bb0...6894d10`.
- Shards: geng res/mod with mod 20000, in the shuffled order `data/shard_order.txt` (seed 585).

## Historical timing estimates

- Measured 03:48-04:12 EDT: about 1.03 shards per second with 16 workers (13-14 s per shard).
- The full census (20000 shards) needs about 5.4 h at that rate, so it does not finish before the
  06:10 cutoff. Expected coverage at 06:10: about 8,700-9,000 of 20,000 shards (about 44%).
- Coverage is recorded exactly: `data/done_shards.txt` (written by the collector).

These early projections are not final coverage. See REG5N16.md for the conditional census conclusion and independent replication limits. The original timed driver is retained as historical source; its dated stop configuration is not a current launch instruction.
