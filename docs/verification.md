# Verification

Evidence belongs to an exact statement and version. The collection does not assign one verification label to an entire problem.

| Evidence | Establishes | Does not establish |
|---|---|---|
| Written proof | A readable argument with stated dependencies | Correctness merely because it exists or received AI review |
| Computation | Results within the recorded input coverage and checker assumptions | An all-orders theorem or an independently replicated census |
| Lean kernel check | A formal declaration follows from its definitions and reported axioms | Fidelity to prose, novelty or human mathematical review |
| Source comparison | Differences from the public statements actually inspected | That a result is new |

For #585, read the [current inventory and historical checks](../problems/585/README.md#build), [v0.4.1 record](../problems/585/findings/V0.4.1.md) and [result index](../problems/585/RESULTS.md). The stated inventory is 78 registered declarations, 77 whole-file oracle checks and 438 configured custom modules. A historical receipt is not a new run after relocation.

The collection scripts require Python 3.11 or later. Individual packages retain their pinned Lean environments.

From the collection root, use:

```bash
python3 scripts/check.py --problem 585 --mode docs
python3 scripts/check.py --problem 585 --mode full
```

The `docs` mode checks collection/package documentation and metadata. It does not prove any theorem. The `full` mode invokes the package’s required verification; inspect its output and preserve failures. A timeout is UNKNOWN, never PASS. The official per-declaration oracle must end with `RESULT: PASS`; allowed axioms and statement checks remain separate requirements. Both #585 and #60 permit only `propext`, `Classical.choice` and `Quot.sound` for registered proved results.

For individual package commands, change into `problems/585/` and use its existing instructions. The root `./check.sh <file> <declaration>` remains a compatibility entrypoint for #585. That wrapper does not check any other problem.

Accepted Lean evidence is reused when the theorem statements, proof terms, transitive imports, pinned toolchain and dependencies, axiom restrictions and verified coverage remain unchanged. The release checks authenticate the evidence and compare its mathematical inputs with the exported package. Documentation, directory, public-base and CI changes alone do not require another proof run. Comment edits require a comparison that preserves executable Lean text. Changed mathematical inputs require verification of the affected proofs and dependent scope. Reuse does not claim a new relocated or hosted build. Historical finite-search coverage and human-review limitations retain their recorded scope.

For [#60](../problems/60/README.md), docs mode checks document identities and links. Full mode also builds its separate Lean package, checks 519 registered types and axiom closures, runs six main-theorem oracles, and replays all 82 configured modules. Its [verification record](../problems/60/VERIFICATION.md) distinguishes the completed resumed gate from a single uninterrupted run, and preserves the exact theorem scope. #585 and #60 have separate proof environments and verification.

For the historical four-thirds theorem in [#643](../problems/643/README.md), full mode builds and kernel-replays 12 configured modules and audits 607 local environment declarations. For [#642](../problems/642/README.md), it builds and replays 264 modules and audits 6,025 declarations. Its ten headline checks cover four whole-graph bounds and six supporting statements. Each package has its own headline oracle, pinned environment and verification record. Counts include aggregate modules and supporting/generated declarations. Both admit only `propext`, `Classical.choice` and `Quot.sound`. Their records distinguish bounded continuations, cached dependencies and unperformed hosted or cold-install checks.

For [#85](../problems/85/README.md), full mode checks the complete projective-incidence repair theorem and its two formal corollaries. It builds and kernel-replays all 65 configured modules, audits the types and axiom dependencies of 1,242 registered declarations, and runs three official theorem oracles. Only `propext`, `Classical.choice` and `Quot.sound` are admitted. The [verification guide](../problems/85/VERIFICATION.md) gives the exact declarations, dependency setup and reproduction commands. Additional written consequences remain labeled separately; the original Erdős #85 question remains open.

The historical four-thirds inventory does not cover the current #643 coefficient-one theorem. Its separate combined proof package passed its exact complete 126-source check, including general design existence and residue-class extremal/forcing equalities. The 23 named probes and 126 kernel replay chunks are scoped in its [verification record](../problems/643/VERIFICATION.md). Human mathematical review remains outstanding.

For [#583](../problems/583/README.md), full reproduction builds and kernel-replays its standalone proof module, audits 1,686 registered declarations and checks three exact headline theorems. Its accepted proof evidence and statement review retain their stated scope.

For [#1017](../problems/1017/README.md), full reproduction follows five explicit library roots, covers 103 modules, audits 1,968 registered declarations and checks five exact headline theorems. Its result index distinguishes fractional and integral statements.

## Continuous integration

Pull requests and pushes to `main` check the current catalogue, documentation, export boundary and mathematical input bindings. Feature-branch pushes do not start a duplicate run. Each Lean package supplies `verification/accepted-mathematical-inputs.json`, which records the exported proof inputs and the coverage of accepted evidence.

To check one package's binding from the collection root:

```bash
python3 -B scripts/check_proof_receipts.py --problem 585 --output /tmp/erdos-585-bindings
```

`MATCH` means the current files and declarations agree with the published binding. The release maintainer authenticates the underlying complete evidence before accepting the binding. A self-consistent JSON file or a successful binding check alone does not establish a proof's correctness or the evidence's origin. The automatic jobs execute no Lean builds, theorem probes, axiom audits or kernel replays.

The manual `workflow_dispatch` action defaults to binding checks. Choosing `mode=full` explicitly requests the full reproduction commands, with an optional problem ID. Full reproduction for #643 selects `macos-15` and requires Darwin arm64, Python 3.11 or later and GNU coreutils `timeout`; other packages use Ubuntu. The combined #643 proof checks its exact Lean and dependency artifact identities. Local accepted evidence does not claim a new hosted proof run. Hosted content and binding results have their own logs and recorded commit identities.
