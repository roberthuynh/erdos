# Erdős Problem 583

[Collection](../../README.md) · [Results](RESULTS.md) · [Proof](Erdos583/Verified.lean) · [Evidence](VERIFICATION.md) · [Manuscript](manuscript.pdf)

## The problem

[Erdős problem 583](https://www.erdosproblems.com/583), Gallai's path-partition conjecture, asks whether every connected simple graph on n vertices has an edge partition into at most ceil(n/2) nonempty vertex-simple paths. Paths partition the original edges exactly.

## Main results

For every connected finite simple graph on n vertices, the general theorem gives at most

$$
\left(\frac23-\frac1{654444}\right)n+\frac16+\frac1{327222}
$$

paths. For a connected graph with every degree even, the bound is

$$
\left(\frac23-\frac1{163611}\right)n+\frac1{54537}.
$$

Both statements have complete Lean proofs with independent AI review of the exact formal sources. The [result index](RESULTS.md) gives their declarations, hypotheses and the supporting parity bound.

## Status

**The general and connected Eulerian partition bounds and the supporting parity baseline are Lean-verified. Human mathematical review remains open.**

The general coefficient improves on 2/3 but does not settle Gallai's conjecture. The integer bound need not improve at every small order. The Eulerian and general results form one bound-improvement family. No exhaustive historical-priority claim is made. The manuscript is a working exposition; its technical exposition is being expanded.

## Prior work

The proof formalizes the parity-sensitive path-partition framework associated with Dean and Kouider, and a four-cycle restriction of the common-root cycle repair used by Chu and Wang. Patel and Yıldız's introduction also records the general undirected baseline. See [sources and reading limits](SOURCES.md).

## Proofs and findings

The [working manuscript PDF](manuscript.pdf) and [TeX source](manuscript.tex) explain the argument. [Verified.lean](Erdos583/Verified.lean) contains the complete standalone proof, including its baseline, restoration, packing and transfer arguments. The original modular structure is preserved in named sections. The package does not assume a restoration theorem, parity baseline or Eulerian bridge as a new axiom. The [result index](RESULTS.md) gives the exact claims and their limits.

## AI use

AI systems developed the proofs, formalization and source reviews. Robert Huynh directed the research. The collection's [AI disclosure](../../README.md#ai-use) applies. No human mathematical review is claimed.

## Verification

From the collection root:

```bash
python3 scripts/check.py --problem 583 --mode docs
python3 scripts/check.py --problem 583 --mode full
```

Docs mode checks file identities and local links. Full reproduction builds and kernel-replays the standalone proof module, audits 1,686 registered declaration types and axiom closures, and runs three headline checks. Use the pinned Lean project and the [verification instructions](VERIFICATION.md). Authenticated evidence can be reused for unchanged mathematical inputs; document checks and binding agreement are not new proof execution. Source identity, axiom checking and kernel replay are separate from manuscript compilation and historical priority.

## Citation and corrections

Use [CITATION.cff](CITATION.cff), together with the exact public source snapshot and declaration name. Corrections and relevant earlier results should identify the exact statement or proof step; see the [contribution guide](../../CONTRIBUTING.md). [NOTICE](NOTICE) records attribution and licensing.
