# Erdős Problem 642

[Collection](../../README.md) · [Results](RESULTS.md) · [Proof](PROOF-MAP.md) · [Evidence](VERIFICATION.md) · [Manuscript](manuscript/main.pdf)

## The problem

[Erdős problem 642](https://www.erdosproblems.com/642) asks whether sufficiently large constant average degree forces a cycle with at least as many chords as vertices. A chord is an original unordered edge between vertices of the cycle, excluding its cycle edges. The graph is finite and simple, and the cycle is simple.

## Main results

There is an absolute constant $C>0$ such that every finite simple graph with $n$ vertices and more than $Cn\log^3(2n)$ edges contains a simple cycle with at least as many distinct chords as vertices. Logarithms are natural. At order zero, the whole edge threshold is defined to be zero.

The package also retains the fifth-power theorem, the adaptive logarithmic improvement, the fourth-power theorem and six supporting statements. These are successive bounds and supporting facts in one development, not ten independent solutions to the original problem. The [result index](RESULTS.md) gives the exact statements and hypotheses.

## Status

**The cubic-logarithmic theorem, earlier whole-graph bounds and six supporting statements have source-bound Lean verification and independent AI review. Human mathematical review remains open.**

The general question of whether a constant multiple of $n$ edges suffices remains open in this work. The manuscript is a working exposition; formal verification does not validate every sentence of it. An announced stronger result limits the comparison with prior work. No current-best or priority claim is made.

## Prior work

Draganić, Methuku, Munhá Correia and Sudakov proved the same chord conclusion from an eighth-power logarithmic density threshold. Draganić's October 2026 preprint announces a stronger essentially log-logarithmic scale; the announcement is not itself a full proof of that result.

The sampling and tough-layer methods draw on Christoph, Hunter and Sudakov's work. The formal development proves its own required interfaces rather than assuming that paper's conclusions as axioms. [Sources and attribution](SOURCES.md) identify the inspected versions, earlier extraction methods and limits of the comparison.

## Proofs and findings

The [working manuscript PDF](manuscript/main.pdf) and [TeX source](manuscript/main.tex) explain dense masks, tough layers, merging and the original-edge count. The [proof map](PROOF-MAP.md) links those mathematical steps to Lean files. The [fifth-power proof guide](PROOF.md) retains the earlier published argument. The [result index](RESULTS.md) distinguishes the current theorem, earlier bounds and supporting statements.

## AI use

AI systems developed the arguments and formalizations and performed the mathematical source reviews. Robert Huynh directed the work. No human mathematical review is claimed. See the [shared AI disclosure](../../README.md#ai-use). Lean checks the formal statements and their proofs; it does not establish historical priority or validate every sentence of the working manuscript.

## Verification

From the collection root:

```bash
python3 scripts/check.py --problem 642 --mode docs
python3 scripts/check.py --problem 642 --mode full
```

Docs mode checks file identities and local links. Full reproduction covers 263 proof modules plus the aggregate import file, audits 6,025 registered declaration types and axiom closures, and runs ten headline checks. A headline check alone does not cover the complete package. Each Lean command has a 240-second limit. A timeout is unknown, never a pass. [Verification details](VERIFICATION.md) describe the accepted evidence, current mathematical input binding and reproduction commands. Authenticated evidence can be reused for unchanged mathematical inputs; document checks and binding agreement are not new proof execution.

The default `check.sh` target remains `Erdos642.Log3V1_20261024.original_log3_rich_cycle`.

## Citation and corrections

Use [CITATION.cff](CITATION.cff) and identify the exact public source snapshot and declaration. Corrections and relevant earlier results should identify the exact statement or proof step; see the [contribution guide](../../CONTRIBUTING.md). [NOTICE](NOTICE) records attribution and licensing.
