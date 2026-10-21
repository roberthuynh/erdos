# Reproduction and evidence boundary

This supplement contains historical mathematical sources, finite computational records and editorial corrections. Current packaging does not constitute new mathematical verification.

## Supplied and external tools

`census/programs/pairc.c` supplies the historical pair tester source; compile it with a C compiler and put the resulting `pairc` on PATH or set PAIRC for entrypoints that support it. `census/pairs-lane/ptool.c` is the separate pair/HD tester source. The nauty 2.9.3 distribution is external; install its `geng`/`genbg` and set executable paths as needed. Python checks use networkx and python-sat where imported. No package versions have been invented for omitted environments.

`papers/quartic/c1checks/run_all.sh` now accepts PY (default python3). `papers/qb5/code/generic_check.py` accepts GENBG (default genbg). `papers/b6-24/c1type/code/c1lib.py` accepts PAIRC and GENBG (defaults pairc and genbg). Their computations were not rerun during editorial preparation.

## Inputs that remain unavailable

Recovered inputs now include the five QB5 classes, pairs review sources/text outputs, original marked-pair source and erroneous streams, the three gen585 validation modules, and the S6 PG(2,5) certificate and review programs. RECOVERED-REPLAY.md records their bounded replays. Historical NOTES/RESUME/M1/M3 notes and original source hash-list documents are excluded; their private operational text is not part of this export. Some original per-graph census certificate streams and interpreter/import layouts remain unavailable here. Records marked [local path], [temporary path], or an executable placeholder remain historical specifications unless explicitly repaired. Missing evidence is not a zero result or mathematical PASS.

The recovered S6 labelled breadth-first output gives levels 9/47/211/1035, with 17 lowering moves from depth-three frames and first escape in four moves. Original T2 streams contain labeling errors; a separate fresh corrected stream now reproduces 66,992 rows with six exactly-two-pairing examples. BM/BM-2 remain unverified hypotheses of their recorded implications. The n16 full-census conclusion remains conditional on coverage, with only sampled independent unpruned replication.

## Hash identity

The original source receipts are not included: their recorded paths and bytes belong to historical source layouts. PROVENANCE.json maps available original source hashes and prior-export hashes to current public file hashes, using only public relative paths. MANIFEST.md inventories this public payload, including the five previously omitted check files. These mappings are not mathematical acceptance. References to omitted FROZEN*.sha256 and other original hash lists identify historical receipts, not runnable checks against this edited export.

## Explicit external configuration gates

REPRODUCTION-CONFIG.json lists 46 redacted executable/import/data paths now replaced with required environment variables. Values must come from the original verified inputs; no guessed replacements are supplied. The three gen585 validators default to bundled validation_tools containing pair_oracle, brute and validate; ERDOS585_VALIDATION_TOOLS can override that directory. The generator executable and nauty directory can be configured with ERDOS585_GEN585 and ERDOS585_NAUTY_DIR. Missing configuration stops the entrypoint. Syntax validation of this configuration handling is not a census replay.

## Numbered references in Lean comments

CoverTransfer (Paper 85), Cubelike (Papers 65/82), CubelikeWitness (65), HaarCycle/HaarDegree/HaarWitness (83), HaarExtraction (85 and HAAR-EXTRACTION-BOUNDARY.md), and HaarSixCycle (83/85) cite historical notes not bundled here. These are not usable public document links. Their Lean imports/declarations give the formal source dependencies; no fresh verification is implied. Lean source bytes are unchanged in this supplement.

## Additional portable configuration and historical timers

Scripts with redacted scratch locations require `ERDOS585_SCRATCH_DIR`, a writable scratch directory; their exact list is in REPRODUCTION-CONFIG.json. Known pairc and ptool executable paths use `PAIRC`/`PTOOL` with command-name defaults. The H22 comparison and S6 spot-check collector now point to the supplied sibling census locations. Historical nauty/Python cache paths identify the original environment, not bundled dependencies. Original dated driver cutoffs are retained as historical parameters and must be configured for any new run; no current launch is asserted here. The LOG/JOBS documents retain dated scientific observations and estimates with obsolete process handles and stop/resume instructions removed.
