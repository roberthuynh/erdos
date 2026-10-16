# Erdős Problem 642

[Collection](../../README.md) · [Result index](RESULTS.md) · [Findings](FINDINGS.md)

## The problem

The [problem](https://www.erdosproblems.com/642) asks whether a constant multiple of n edges forces an n-vertex graph to contain a cycle with at least as many chords as cycle vertices.

A chord is an actual graph edge joining two nonconsecutive vertices of the cycle. It is not a missing edge or an edge of the cycle itself. Chords are counted as distinct unordered edges.

## Main results

**Lean-checked theorem; AI-written and AI-reviewed. No human mathematical review.**

There is an absolute constant C > 0 such that every finite simple graph G on n vertices satisfying

$$e(G) > C n\bigl(\log(2n)\bigr)^5$$

contains an actual simple cycle with at least its length in distinct actual chords. The logarithm is natural. The same C works for every graph and every order; no regularity, expansion or spectral hypothesis remains in the final theorem. The empty and singleton cases are vacuous. The theorem does not provide a useful small numerical C.

The [formal theorem](Openmath/Erdos642/Proofs/CampaignFe72210bContinuation3/OriginalBound.lean) and its declaration are indexed in [RESULTS.md](RESULTS.md). This package claims only the fifth-power bound stated above.

## Status

The result improves a logarithmic factor in the edge threshold. It does not settle the original linear-threshold question in Erdős #642. Worldwide priority remains unresolved; the [source comparison](SOURCES.md) records the inspected versions and limits.

## Prior work

Draganić, Methuku, Munhá Correia and Sudakov published an O(n(log n)^8) bound in 2024. A public 2026 discussion sketch already claims the seventh power, so that exponent is not presented here as new. The exported result gives the fifth power through a formalized extraction and random-walk argument. Draganić and Girão’s 2026 preprint guarantees almost linearly many chords in the cycle length, which is a different conclusion. The original O(n) question remains open.

The [source comparison](SOURCES.md) records exact versions, reading limits and unresolved priority questions.

## Proofs and findings

The [mathematical exposition](PROOF.md) explains the extraction, fourth-return estimate, shared random-walk events and parameter choices giving the fifth power. The [formal proof map](PROOF-MAP.md) links the full 134-module dependency chain. The exposition identifies the analytic suppliers it uses; the Lean source provides their complete proofs. The [findings](FINDINGS.md) explain the contribution and its boundaries; the [result index](RESULTS.md) identifies the exact formal claim.

## AI use

AI agents prepared the Lean proofs and exposition. Separate agents in fresh contexts reviewed the package, including reviewers from the same model family. See the [shared AI disclosure](../../README.md#ai-use). These are AI reviews, not human or institutional endorsements. This package has its own Lean verification.

## Verification

From the collection root:

```bash
python3 scripts/check.py --problem 642 --mode docs
python3 scripts/check.py --problem 642 --mode full
```

Docs mode checks local links and frozen source and document identities. Full mode builds and kernel-replays all 135 configured modules, checks the exact types and axiom closures of 2,163 registered declarations, and runs the main-theorem oracle. The declaration count includes supporting and generated declarations. [Verification details](VERIFICATION.md) record the completed checks, pinned dependencies and reproducibility limits. Novelty and human mathematical review are separate.

## Citation and corrections

Use the [problem citation](CITATION.cff) and identify the exact source snapshot. This package has no assigned version or DOI; identify it by its Git commit. Corrections should identify the declaration, proof step or earlier source; see the [contribution guide](../../CONTRIBUTING.md).
