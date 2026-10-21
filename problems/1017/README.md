# Erdős Problem 1017

[Collection](../../README.md) · [Results](RESULTS.md) · [Proof](PROOF-MAP.md) · [Evidence](VERIFICATION.md) · [Manuscript](manuscript/main.pdf)

## The problem

The [original question](https://www.erdosproblems.com/1017) asks for estimates of f(n,k) when k > n²/4, where f(n,k) is the maximum, over n-vertex graphs with k edges, of the minimum number of cliques in an integral edge partition. The cliques partition the original edges exactly.

## Main results

This package contains finite bounds for exact fractional clique partitions, a construction at a prescribed edge count, and an exact extremum for binomial clique costs.

| Result | Scope | Main source |
| --- | --- | --- |
| Density-dependent upper bound with coefficient √7/3 | Every finite simple graph; exact fractional edge loads | [SharpAffine.lean](Erdos1017/SharpAffine.lean) |
| Finite lower construction at exactly ⌊n²/4⌋ + m edges | n ≥ 100, 2n ≤ m, 100m ≤ n²; fractional and integral partitions | [MesoscopicLower.lean](Erdos1017/MesoscopicLower.lean) |
| Exact binomial-cost extremum | Every n ≥ 0 and t ≥ 2; fractional covers and decompositions of t-cliques | [BinomialSharp.lean](Erdos1017/BinomialSharp.lean) |
| Obstruction to every larger anchored slope | A finite split graph for each λ > √7/3 | [SlopeBarrier.lean](Erdos1017/SlopeBarrier.lean) |
| Near-complete upper bound | Exact fractional cost at most n² − 2e(G) | [NearComplete.lean](Erdos1017/NearComplete.lean) |

The [result index](RESULTS.md) gives the exact declarations, hypotheses and conclusions. Fractional, integral and binomial-cost statements have different scopes.

## Status

**The five stated conclusions have complete Lean proofs and independent AI source reviews. No human mathematical review is claimed.**

These fractional and weighted results leave the original integral estimation problem open. The package does not claim a finite integral upper bound or a complete solution of Erdős #1017. The manuscript is a working exposition; the formal declarations specify the exact proved hypotheses and conclusions. Lean verification does not establish novelty or historical priority.

## Prior work

The graph reductions use the classical Zykov averaging framework. Split graphs, signed dual certificates and elementary subset counting also have classical antecedents; this package does not claim those general ideas originated here.

The [sources and attribution](SOURCES.md) distinguish the packing comparison of Balogh and Wigal, the edge-and-triangle decompositions of Blumenthal and coauthors, and the general fractional-cost framework and external asymptotic rounding theorem of Balogh and coauthors. That rounding theorem is outside this package's five formal conclusions. Historical priority is not exhaustively established.

## Proofs and findings

The [working manuscript PDF](manuscript/main.pdf) and [TeX source](manuscript/main.tex) explain the statements and constructions. The [proof map](PROOF-MAP.md) links the main arguments to Lean, including the supporting selectors, signed certificates and rational cells. The [result index](RESULTS.md) keeps the exact scopes explicit.

## AI use

AI systems developed arguments, Lean proofs and source reviews under Robert Huynh's direction. Robert Huynh is the sole named author. No human mathematical review is claimed. See the [shared AI disclosure](../../README.md#ai-use).

## Verification

From the collection root:

```bash
python3 scripts/check.py --problem 1017 --mode docs
python3 scripts/check.py --problem 1017 --mode full
```

Docs mode checks file identities and local links. Full reproduction builds and kernel-replays all 103 local modules in the union of the five import closures, audits 1,968 registered declaration types and axiom closures, and runs five headline checks. [Verification details](VERIFICATION.md) describe the pinned dependencies, accepted evidence, current mathematical input binding and reproduction commands. Authenticated evidence can be reused for unchanged mathematical inputs; document checks and binding agreement are not new proof execution. Manuscript compilation and historical priority remain separate.

## Citation and corrections

Use [CITATION.cff](CITATION.cff) and identify the exact public source snapshot and declaration. Corrections and relevant earlier results should identify the exact statement or proof step; see the [contribution guide](../../CONTRIBUTING.md). [NOTICE](NOTICE) records attribution and licensing.
