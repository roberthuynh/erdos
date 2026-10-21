# excensus jobs

Launched 2026-10-05 23:54:22 EDT. One driver, 3 workers, `nice -n 10`, detached with `nohup`.
No shard starts at or after 06:00 EDT; every shard runs under `timeout` that ends at 06:58 EDT.
When the workers finish (queue done, cutoff, or STOP), the driver runs `code/collect.py`, which
writes `data/COLLECT.md` and the results block of `EX.md`.

## Historical output layout

| What | Value |
|---|---|
| Driver log | `logs/driver.log` (one line per finished shard) |
| Job table | `code/jobs.tsv` |
| Work list | `code/queue.txt` (440 lines, run in order: A, then B, then C) |
| Shard files | `logs/<tag>/shard_<r>.{g6,err,done}`; a shard counts only if its `.done` exists |

## Jobs

Binary for all three: `<Q4_GENBG_EXECUTABLE>`
(SHA-256 `a29067acd4d5a611fb56321f5eed7910bf90fc6db7712d0261eec4ebbd84404c`), output = graphs with
no 4-regular subgraph.

| Tag | Command (shard r of mod) | Shards | Projected core-s (pilot fit; ×1.45 at the measured historical load) | Why |
|---|---|---|---|---|
| A `n18_99_e47` | `genbg_q4 -X-2 -d4:4 -D6:6 9 9 47:47 r/40` | 40 | 1,340 (1,950) | last piece of n = 18 at e = 3n − 7 |
| B `n19_910_e50` | `genbg_q4 -X-2 -d4:4 -D6:6 9 10 50:50 r/200` | 200 | 23,400 (34,000) | n = 19 at e = 3n − 7 (sides forced 9 + 10) |
| C `n20_1010_e54_d5` | `genbg_q4 -X-2 -d5:5 -D6:6 10 10 54:54 r/200` | 200 | 5,800 (8,400) | n = 20 at e = 3n − 6, where Lemma B forces δ ≥ 5 |

Total projected: 30,500 core-s at pilot speed (8.5 core-h). Measured on job A at the measured historical load
(load average 78 to 156): 1.5 times the pilot CPU per shard and about 78% of a core per worker, so about
46,000 core-s (12.9 core-h) plus about 0.6 core-h of pilots: about 13.5 core-h, roughly 12% over the
12 core-h guide. The historical estimate allocated the remaining time to C after B.
ETA: about 02:45 EDT at pilot speed; about 05:30 EDT at the measured historical load. If the run is cut at 06:00,
the cut falls on C first.

Update 00:17 EDT: job A complete (40/40, 0 graphs, 2,057 core-s), so ex(18) = 46. B's first shard took
140 s (1.2 times its pilot), so B is about 28,000 core-s and C about 7,000: total about 11 core-h with
pilots, inside the guide. Revised ETA: B about 03:35 EDT, C about 04:35 EDT.


These are dated run records and pilot projections, not current execution instructions. Final coverage is in the companion result report. Original inputs and executable identities are subject to REPRODUCTION-BOUNDARY.md at the supplement root.
