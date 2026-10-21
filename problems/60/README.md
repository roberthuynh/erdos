# Erdős Problem 60

[Collection](../../README.md) · [Results](RESULTS.md) · [Proof](LINEAR-RANGE-THEOREM.md) · [Evidence](VERIFICATION.md) · [Manuscript](manuscript/main.pdf)


## The problem

The [Erdős–Simonovits question](https://www.erdosproblems.com/60) asks whether every graph on n vertices with more than ex(n,C4) edges contains at least a constant multiple of sqrt(n) copies of C4.

A C4 is a cycle of four distinct vertices. The extremal number ex(n,C4) is the most edges an n-vertex graph can have without one. The question asks how many four-cycles must appear once that threshold is exceeded. Copies need not be induced.

## Main results

**Lean-checked theorem; AI-written and AI-reviewed. No human mathematical review.**

For integers n≥1 and 1≤t≤n(n−1)/2−ex(n,C4), let h(n,t) be the minimum number of ordinary unlabelled C4 copies in a simple graph on n vertices with exactly ex(n,C4)+t edges. Copies need not be induced.

The [theorem and written proof](LINEAR-RANGE-THEOREM.md), with [Lean verification](VERIFICATION.md), establish that for every power of two q≥10^16 and every integer 1≤t≤10^-8 q,

h(q²+q+1,t)=t(q−1).

Equality graphs are orthogonal polarity graphs of projective planes of order q with a matching of t edges added between absolute vertices. For arbitrary even integers q≥10^16, the theorem instead uses exactly M+t edges, where M=q(q+1)²/2. It does not assert ex(q²+q+1,C4)=M or plane existence at every even order.

This package does not cover the entire q/2 conjectural surplus range. The [result index](RESULTS.md) also records the separate first-excess structural statement.

## Status

The theorem covers only the orders and surplus range stated above. It does not settle unrestricted Erdős #60. Worldwide priority remains unresolved; the source-comparison limits are recorded below.

## Prior work

He, Ma and Yang's published 2023 result gives the same exact value and matching equality classification for sufficiently large powers of two in the range 1≤t<q^(1/8)/30. The proposed contribution is the extension to the stated uniform linear interval and its structural argument. The first-excess values and matching constructions are already known.

Their [Theorem 1.6(B)](https://doi.org/10.4208/csiam-am.SO-2021-0006) also gives h(q²+q+1,t) ≥ (1/2+o(1))tq and h(q²+q+1,t) = Θ(tq+t⁴/q⁸), for feasible positive t as q tends to infinity through powers of two. The proposed extension concerns the exact minimum and equality cases, not a new asymptotic order of magnitude.

The [literature comparison](LITERATURE-COMPARISON.md) identifies inspected versions and exact differences. Full journal comparison for Qiao–Zhan and journal-version differences for Gerbner–Nagy–Vizer remain unchecked; successor coverage is bounded. Worldwide priority is unresolved.

## Proofs and findings

The [working manuscript PDF](manuscript/main.pdf) and [TeX source](manuscript/main.tex) present the stated linear-range theorem and its proof.

Start with the [findings](FINDINGS.md) and [theorem and written proof](LINEAR-RANGE-THEOREM.md), then its linked localization, linear-support, completion and retained-path arguments. [Sources](SOURCES.md) states the external mathematical inputs and their attribution. The [result index](RESULTS.md) gives the exact claims and their limits.

## AI use

AI agents prepared the written proofs, Lean formalization and exposition. Separate agents in fresh contexts reviewed them, including reviewers from the same model family. See the [shared AI disclosure](../../README.md#ai-use). These reviews are not human endorsements. This package has its own Lean verification, separate from #585.

## Verification

From the collection root:

```bash
python3 scripts/check.py --problem 60 --mode docs
python3 scripts/check.py --problem 60 --mode full
```

The docs mode checks local links and recorded document identities. Full mode additionally builds the Lean package, audits all 519 registered declaration types and axiom closures, runs the six main-theorem oracles and replays all 82 configured modules through the kernel. The package pins Lean 4.33.1 and mathlib. [Verification details](VERIFICATION.md) record the completed checks, exact declarations and reproducibility commands. Novelty and human mathematical review are separate. Written-document versions are recorded in [source-identity.json](source-identity.json).

## Citation and corrections

Use the [problem citation](CITATION.cff) and identify the exact source snapshot. It describes an unpublished result and formalization, with no assigned release version or DOI. Corrections and prior-work references should name the exact claim or proof step; see the [contribution guide](../../CONTRIBUTING.md).
