# Verification and its limits

[Overview](README.md) · [Results](RESULTS.md) · [Dated record](findings/supplement/checks/v0.4.1/verification.json)

## Recorded formal evidence

The [v0.4.1 verification record](findings/supplement/checks/v0.4.1/verification.json), dated October 15, 2026, records a successful build, type and axiom checks for 78 registered proved declarations, 77 whole-file theorem oracles and kernel replay of 438 configured custom modules. It binds the recorded sources, checking tools, Lean toolchain and dependency revisions. This is historical source-bound evidence, not a fresh check of changed files.

The registered proved results use only `propext`, `Classical.choice` and `Quot.sound`; no registered proved result depends on `sorryAx`. Each applicable `check.sh` must report `RESULT: PASS`. One registered declaration in [Openmath/Target.lean](Openmath/Target.lean) has statement/axiom and kernel evidence but no whole-file oracle because the file also contains unproved conjectures. The declaration count includes supporting results, not 78 independent discoveries.

The [dated reproduction account](findings/V0.4.1.md#reproduction-and-responsibility) explains the record and its limits. Exact declarations are listed in the [theorem registry](scripts/headline-theorems.json); the [result index](RESULTS.md) separates formal results, computational exclusions and written candidates.

## Reproduce

Formal reproduction requires elan, the pinned Lean and Mathlib dependencies, Python 3.11 or later, and GNU `timeout` (coreutils). Census reproduction additionally requires a C compiler and nauty 2.9.3. Download the pinned Mathlib cache from `problems/585/` with `lake exe cache get`. From the collection root:

```bash
python3 scripts/check.py --problem 585 --mode docs
python3 scripts/check.py --problem 585 --mode full
```

Docs mode checks metadata and links. Full mode runs package checks, configured module builds, the statement/axiom audit, registered whole-file oracles and kernel replays. Each Lean replay has its own 240-second timeout. A timeout is unknown. See the [collection verification guide](../../docs/verification.md).

## Evidence boundaries

These formal checks do not regenerate the full finite census or replay every finite-certificate stream. The upper exclusions for f(11) and f(12) remain computational; their lower witnesses have Lean checks. Canonical generation is shared, and separate certificate checking is not an independent graph census. The complete 16-vertex census exclusion has not been independently replicated in full. See the [finite-certificate guide](findings/supplement/small-values/certificates/README.md) and [census account](findings/FINDINGS.md#appendix-c-census-details).

The [proof companion](findings/V0.4-PROOF.md) and working manuscript are partial expositions. Written and conditional arguments retain the assumptions and computational dependencies listed in the [findings](findings/FINDINGS.md#4-results). Formal verification of registered declarations does not verify every written candidate, settle the original problem, establish novelty or constitute human mathematical review. AI agents produced the work and separate AI agents reviewed it; the [shared disclosure](../../README.md#ai-use) applies.
