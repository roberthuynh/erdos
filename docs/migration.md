# Collection migration

The repository now gives each released problem its own package. The existing #585 project moves as a unit to `problems/585/`. Its Lean module names, package-relative paths, dependency pins and historical records remain intact. This structural change adds no mathematical result and does not renew historical verification claims.

| Previous root path | Package path |
|---|---|
| `Openmath/`, `Openmath.lean`, `Axioms.lean` | `problems/585/` followed by the same path |
| `R643.lean`, other Lean files and module directories | `problems/585/` followed by the same path |
| `findings/`, `literature/`, `graphs/`, `computations/`, `census/` | `problems/585/` followed by the same path |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | `problems/585/` followed by the same path |
| Problem-specific `scripts/`, `check.sh` | `problems/585/` followed by the same path |
| #585 `CITATION.cff`, `LICENSE`, `NOTICE` | `problems/585/` followed by the same path |

Root documentation, the collection registry, shared checks and export policy describe the collection. The root citation describes the collection; the #585 citation retains its own version. Existing tags and commit history remain historical references to their original layout. Old receipts keep their original bytes and paths.

`R643.lean` is a #585 module in namespace `Erdos585.QB7SmallLobeR643`; it is not an Erdős #643 package.

To reproduce existing Lake and package commands in a fresh clone:

```bash
git clone https://github.com/roberthuynh/erdos.git
cd erdos/problems/585
```

Then follow the [package build instructions](../problems/585/README.md#build). For an existing checkout, first change into its absolute `problems/585` directory. Root Lake commands have moved to that directory. Legacy root `./check.sh <file> <declaration>` calls forward to #585; source arguments remain relative to the #585 package. Collection checks run from the root as documented in the [verification guide](verification.md).

The [complete path map](path-map.json) records every file from the public baseline, its destination and original SHA-256. The main findings, decisions, release-note and literature landing pages retain navigation stubs.

In preserved historical #585 notes, “repository root” means the former #585 root. Run their package commands from `problems/585/` now; for example, the `graphs/verify_graphs.py` command in the v0.4.1 note is relative to that directory.
