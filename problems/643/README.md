# Erdős Problem 643

[Collection](../../README.md) · [Result index](RESULTS.md) · [Findings](FINDINGS.md)

## The problem

The [problem](https://www.erdosproblems.com/643) asks how many edges force a generalized four-cycle in a uniform hypergraph. This package concerns uniformity three, where the question asks whether the forcing threshold is asymptotic to binom(n,2).

A 3-uniform hypergraph is a collection of three-element vertex sets. The forbidden configuration consists of four distinct triples A, B, C, D such that A and B are disjoint, C and D are disjoint, and A ∪ B = C ∪ D. Each pair partitions the same six vertices. Extra triples on those vertices are allowed.

## Main results

**Lean-checked theorem; AI-written and AI-reviewed. No human mathematical review.**

For every finite vertex set V of size n and every family H of three-element subsets of V avoiding that configuration,

$$|H| \le \left\lfloor \frac{4}{3}\binom{n}{2} \right\rfloor.$$

There are no additional density, codegree or structural hypotheses. The bound includes all nonnegative orders n. The maximum avoiding size therefore satisfies the same bound; the minimum forcing threshold is at most that integer plus one. The Lean theorem proves the per-family inequality. Extremal and forcing functions are written corollaries, not separate formal declarations.

The [formal theorem](Openmath/Erdos643/FinalBound.lean) and its declaration are indexed in [RESULTS.md](RESULTS.md). This package claims only the coefficient bound stated above.

## Status

The result improves the upper-bound coefficient from 13/9 to 4/3. It does not reach the conjectured coefficient one or settle Erdős #643. Worldwide priority remains unresolved; the [source comparison](SOURCES.md) records the inspected versions and limits.

## Prior work

Pikhurko and Verstraëte proved the all-order bound (13/9) binom(n,2) in 2009. The package lowers that coefficient to 4/3: a saving of (1/9) binom(n,2), or 1/13 of the earlier coefficient. Their graph deletion and hypergraph cleaning lemmas are essential antecedents. Huang, Ma and Yang’s 2026 preprint supplies a related deletion framework and solves the fixed-uniformity r≥4 case for sufficiently large n; its theorem does not settle r=3. The conjectured coefficient one remains open.

The [source comparison](SOURCES.md) records exact versions, reading limits and unresolved priority questions.

## Proofs and findings

[Written proof](PROOF.md) gives the argument using explicitly attributed Pikhurko–Verstraëte lemmas. The [formal proof map](PROOF-MAP.md) connects the 11 proof modules to the full theorem. These lemmas are proved in the formal dependency closure, not assumed as axioms. The [findings](FINDINGS.md) explain the contribution and its boundaries; the [result index](RESULTS.md) identifies the exact formal claim.

## AI use

AI agents prepared the written proof, Lean formalization and exposition. Separate agents in fresh contexts reviewed the package, including reviewers from the same model family. See the [shared AI disclosure](../../README.md#ai-use). These are AI reviews, not human or institutional endorsements. This package has its own Lean verification.

## Verification

From the collection root:

```bash
python3 scripts/check.py --problem 643 --mode docs
python3 scripts/check.py --problem 643 --mode full
```

Docs mode checks local links and frozen source and document identities. Full mode builds and kernel-replays all 12 configured modules, checks the exact types and axiom closures of 607 registered declarations, and runs the main-theorem oracle. The declaration count includes supporting and generated declarations. [Verification details](VERIFICATION.md) record the completed checks, pinned dependencies and reproducibility limits. Novelty and human mathematical review are separate.

## Citation and corrections

Use the [problem citation](CITATION.cff) and identify the exact source snapshot. This package has no assigned version or DOI; identify it by its Git commit. Corrections should identify the declaration, proof step or earlier source; see the [contribution guide](../../CONTRIBUTING.md).
