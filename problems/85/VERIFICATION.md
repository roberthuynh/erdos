# Verification

The full stated repair theorem and its two corollaries have official Lean `RESULT: PASS`, zero holes and only `propext`, `Classical.choice`, and `Quot.sound`. No human mathematical review is claimed. The original Erdős #85 question remains open; verification does not establish novelty or priority.

## Exact declarations

| Declaration in `Erdos85.IncidenceRepair` | Source | Statement |
|---|---|---|
| `projective_incidence_repair` | `Openmath/IncidenceRepair/Main.lean` | `RepairClaim K L n`, full conditional repair |
| `repair_dichotomy` | `Openmath/IncidenceRepair/Corollaries.lean` | Unconditional collapse/repair dichotomy |
| `frameSurvival_bound_of_no_field_embedding` | `Openmath/IncidenceRepair/Corollaries.lean` | No-field-embedding survival bound |

The near-one-survival estimate in RESULTS item 2 is a written union-bound consequence of R1, not a separately checked Lean declaration. The numerical characteristic/divisibility criterion in item 3 is the classical interpretation of the formal no-field-embedding hypothesis.

The theorem permits arbitrary finite fields, arbitrary point and hyperplane maps and n≥2. Under positive ordered-frame survival ρ and δ≤ρ/(10^9 n²), one field embedding and one coupled linear action repair both maps with D≤5T/q^(n−1)≤10T/d. T counts original broken flags. No geometric supplier assumptions remain.

## Reproduce

Install the pinned Lean toolchain through elan. The pinned dependencies must be available (Lake may fetch them on the first build). From the collection root:

```sh
python3 scripts/check.py --problem 85 --mode docs
python3 scripts/check.py --problem 85 --mode full
```

Docs mode checks identities and links only. Full mode runs negative controls, builds the entire 65-module local closure, compares all declaration types and axiom dependencies against the frozen registry, runs all three official `check.sh` oracles and kernel-replays every local module. Each Lean subprocess is bounded at 240 seconds. A timeout is UNKNOWN.

The individual oracle can also be run from `problems/85`:

```sh
timeout 240 bash check.sh Openmath/IncidenceRepair/Main.lean Erdos85.IncidenceRepair.projective_incidence_repair
timeout 240 bash check.sh Openmath/IncidenceRepair/Corollaries.lean Erdos85.IncidenceRepair.repair_dichotomy
timeout 240 bash check.sh Openmath/IncidenceRepair/Corollaries.lean Erdos85.IncidenceRepair.frameSurvival_bound_of_no_field_embedding
```

Each must report `RESULT: PASS`. Source or pin changes require renewed checking and statement review. The commands above produce the theorem-oracle output and collection check receipts. Record the exact Git commit when reproducing a result. The frozen source and declaration inventories are `scripts/proof-modules.json` and `scripts/headline-theorems.json`.
