# Reproducing the proof checks

The package pins Lean 4.33.1, formal_conjectures at 137aec5c7abd3aa61f7a73138a97279acfc79e93 and Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474. `lake-manifest.json` pins transitive dependencies. GNU `timeout` is required. Commands below run from this package directory.

```sh
lake exe cache get
timeout 240 lake build Erdos583.Verified
timeout 240 python3 -B scripts/check_axioms.py
timeout 240 bash check.sh Erdos583/Verified.lean Erdos583.general_path_partition_improvement
timeout 240 bash check.sh Erdos583/Verified.lean Erdos583.eulerian_path_partition_improvement
timeout 240 bash check.sh Erdos583/Verified.lean Erdos583.hasPathBound_phi
timeout 240 python3 -B scripts/replay_modules.py --module Erdos583.Verified
```

The official oracles must print `RESULT: PASS`; the statement audit must print `STATEMENTS: PASS`; kernel replay must print `KERNEL REPLAY: PASS`. A timeout is unknown, not success. The collection runs the full configured package plan through `scripts/check.py`.

The proof permits only `propext`, `Classical.choice` and `Quot.sound`. Source scans reject missing proofs and native or unsafe kernel shortcuts. The statement audit compares the complete local declaration inventory, types and axiom closures with the registered record. Replay checks the whole local import closure, which is the standalone module. Every local proof source is included, and dependency revisions remain pinned.

The original standalone source received independent exact-source acceptance and full clean verification on 22 October 2026. Public-copy transformations affect comments only and are recorded by hash in `source-identity.json`. The [accepted mathematical input record](verification/accepted-mathematical-inputs.json) identifies the source, declaration types, axiom closures, pinned dependencies and accepted evidence. Authentication of that evidence and agreement of mathematical inputs permit reuse after these comment-only edits. A binding match alone does not authenticate the evidence or prove a theorem. The [collection guide](../../docs/verification.md) distinguishes that reuse from the optional full reproduction above; a change to mathematical inputs requires verification of the affected scope. These mathematical checks do not certify historical novelty, human review or the accuracy of newly written exposition.
