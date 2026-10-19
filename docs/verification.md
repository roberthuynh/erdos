# Verification

Evidence belongs to an exact statement and version. The collection does not assign one verification label to an entire problem.

| Evidence | Establishes | Does not establish |
|---|---|---|
| Written proof | A readable argument with stated dependencies | Correctness merely because it exists or received AI review |
| Computation | Results within the recorded input coverage and checker assumptions | An all-orders theorem or an independently replicated census |
| Lean kernel check | A formal declaration follows from its definitions and reported axioms | Fidelity to prose, novelty or human mathematical review |
| Source comparison | Differences from the public statements actually inspected | That a result is new |

For #585, read the [current inventory and historical checks](../problems/585/README.md#build), [v0.4.1 record](../problems/585/findings/V0.4.1.md) and [result index](../problems/585/RESULTS.md). The stated inventory is 78 registered declarations, 77 whole-file oracle checks and 438 configured custom modules. A historical receipt is not a new run after relocation.

From the collection root, use:

```bash
python3 scripts/check.py --problem 585 --mode docs
python3 scripts/check.py --problem 585 --mode full
```

The `docs` mode checks collection/package documentation and metadata. It does not prove any theorem. The `full` mode invokes the package’s required verification; inspect its output and preserve failures. A timeout is UNKNOWN, never PASS. The official per-declaration oracle must end with `RESULT: PASS`; allowed axioms and statement checks remain separate requirements. Both #585 and #60 permit only `propext`, `Classical.choice` and `Quot.sound` for registered proved results.

For individual package commands, change into `problems/585/` and use its existing instructions. The root `./check.sh <file> <declaration>` remains a compatibility entrypoint for #585. That wrapper does not check any other problem.

A directory migration requires fresh verification at final paths. Unchanged source hashes preserve identity, but do not establish a successful relocated build. Historical finite-search coverage and human-review limitations retain their original scope unless a new check explicitly changes them.

For [#60](../problems/60/README.md), docs mode checks document identities and links. Full mode also builds its separate Lean package, checks 519 registered types and axiom closures, runs six main-theorem oracles, and replays all 82 configured modules. Its [verification record](../problems/60/VERIFICATION.md) distinguishes the completed resumed gate from a single uninterrupted run, and preserves the exact theorem scope. #585 and #60 have separate proof environments and verification.

For [#643](../problems/643/README.md), full mode builds and kernel-replays 12 configured modules and audits 607 local environment declarations. For [#642](../problems/642/README.md), it builds and replays 135 modules and audits 2,163 declarations. Each package has its own headline oracle, pinned environment and verification record. Counts include aggregate modules and supporting/generated declarations. Both admit only `propext`, `Classical.choice` and `Quot.sound`. Their records distinguish bounded continuations, cached dependencies and unperformed hosted or cold-install checks.

For [#85](../problems/85/README.md), full mode checks the complete projective-incidence repair theorem and its two formal corollaries. It builds and kernel-replays all 65 configured modules, audits the types and axiom dependencies of 1,242 registered declarations, and runs three official theorem oracles. Only `propext`, `Classical.choice` and `Quot.sound` are admitted. The [verification guide](../problems/85/VERIFICATION.md) gives the exact declarations, dependency setup and reproduction commands. Additional written consequences remain labeled separately; the original Erdős #85 question remains open.
