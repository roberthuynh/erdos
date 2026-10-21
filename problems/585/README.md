# Erdős Problem 585

[Collection](../../README.md) · [Results](RESULTS.md) · [Proof](findings/V0.4-PROOF.md) · [Evidence](VERIFICATION.md) · [Manuscript](manuscript/main.pdf)


## The problem

What is the maximum number of edges that a graph on n vertices can have if it does not contain two edge-disjoint cycles with the same vertex set?

The two cycles must visit exactly the same vertices, but cannot share an edge. They may use only part of the graph. Write f(n) for the maximum number of edges in an n-vertex graph with no such pair. See the [original problem](https://www.erdosproblems.com/585).

## Main results

### Regular subgraphs

Let G be a finite simple bipartite graph on n ≥ 2q vertices, with maximum degree at most 2q − 2. Write e for its number of unordered edges and D = (q − 1)n − e. The following Lean-checked bounds force a nonempty q-regular subgraph using original vertices and edges:

| Parameters | Sufficient deficit bound |
|---|---|
| Integers h ≥ 6 and q ≥ 4096(h + 1)² | D ≤ hq − 16h² |
| Integer q ≥ 200704 | D ≤ q^(3/2)/128 |

The power is interpreted over the reals; the second bound is equivalent to D ≤ floor(q^(3/2)/128). These results allow the subgraph to use a subset of the vertices; they do not promise spanning, induced or connected support. The [v0.4 note](findings/V0.4.md) gives the parameterized theorem and earlier bounds. The [v0.4.1 note](findings/V0.4.1.md#smaller-cutoff-corollary) gives the smaller-cutoff corollary. A regular subgraph need not contain the cycle pair required by Erdős #585.

For every integer q ≥ 5 and n ≥ 4q − 5, a Lean-checked [avoiding family](findings/V0.4.md#parameterized-obstruction-and-exponent-gap) gives a bipartite graph of maximum degree at most 2q − 2 with exactly (q − 1)n − (q² − 3q + 4) edges and no nonempty q-regular subgraph. Thus a universal sufficient deficit allowance in this class cannot exceed q² − 3q + 3. Together with the parameterized theorem, this leaves a gap between allowances of order q^(3/2) and q²; the optimal exponent remains open in this work.

For q = 4, every finite simple bipartite graph with n ≥ 4, maximum degree at most six and at least 3n − 6 edges has a nonempty 4-regular subgraph. Avoiding examples with 3n − 8 edges exist for every n ≥ 11. Whether 3n − 7 always suffices remains open in this work.

### Verified in Lean

Other formal results include f(n) = n(n−1)/2 for n ≤ 4; f(5) = 9, f(6) = 12 and f(7) = 16; lower-bound constructions; and pair-free 5-regular graphs on 18 and 32 vertices, plus a bipartite one on 104 vertices. Exact statements and source declarations are in the [findings](findings/FINDINGS.md#1-claims-and-evidence) and [theorem registry](scripts/headline-theorems.json).

### Computations

**Computational exact values, with Lean-checked lower witnesses.** The reported values f(11) = 31 and f(12) = 36 combine Lean-checked lower witnesses with computational upper exclusions. The [finite-certificate guide](findings/supplement/small-values/certificates/README.md) gives the evidence and checks. The upper exclusions share nauty's canonical generation; separate certificate checking is not an independent graph census.

### Census

**Lean-checked existence; computational minimality.** The reported minimum order of a pair-free 5-regular graph is 18. Existence at 18 is Lean checked; minimality depends on the finite census. The complete 16-vertex exclusion has not been independently replicated in full. See the [census account](findings/FINDINGS.md#appendix-c-census-details) and [commands](census/programs/COMMANDS.md).

## Status

The original problem is open in the sources checked in October 2026. None of the results here improves its known asymptotic bounds.

## Prior work

The known bounds are f(n) ≥ c·n log log n (Pyber, Rödl and Szemerédi, 1995) and f(n) ≤ n (log n)^O(1) (Chakraborti, Janzer, Methuku and Montgomery, Adv. Math. 2025; arXiv 2024). The explicit linear lower bounds here are smaller asymptotically. Exact values through n = 10 were reported by [Erdős Problem a Day](https://erdosproblemaday.com/report/585) on July 28, 2026; this repository reproduces them.

The [literature comparison](literature/README.md) records the closest regular-subgraph results, source versions, attribution and remaining gaps. It includes credit for Alejandro Zarzuelo Urdiales's dated public review. Worldwide novelty and a separate new application of the regular-subgraph bounds have not been established.

## Proofs and findings

The [working manuscript PDF](manuscript/main.pdf) and [TeX source](manuscript/main.tex) give a partial exposition of the regular-subgraph results. They do not expand every selection or counting argument; the Lean sources provide the formal evidence.

The [full findings](findings/FINDINGS.md) give definitions, claims, evidence and open questions. The [result index](RESULTS.md) links each line of work. The [proof companion](findings/V0.4-PROOF.md) is a partial exposition of the regular-subgraph argument; some selection and counting arguments remain unexpanded. The Lean sources provide the formal evidence for those results.

### Written proofs (AI-written and AI-reviewed)

The written candidates include a cycle pair in every bipartite 6-regular graph on at most 24 vertices, an equivalence with the vertex-deleted formulation, and conditional routes to asymptotic bounds. Their assumptions and computational dependencies are recorded in the [findings](findings/FINDINGS.md#4-results). These arguments have AI reviews but no human mathematical review. The [request for proof review](../../README.md#help-needed) is on the collection homepage.

### The formal statement

[Openmath/Target.lean](Openmath/Target.lean) defines `maxEdges` and the cycle-pair predicate. It contains the statement proposed to [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures), alongside unproved conjectures. No human Lean expert review is claimed.

## AI use

AI agents produced the statements, proofs, constructions and search programs. Separate-agent reviews are AI reviews; no human mathematical review is claimed. See the [shared AI disclosure](../../README.md#ai-use), [How this was made](../../README.md#how-this-was-made), and the [model contribution record](findings/FINDINGS.md#7-ai-use-and-model-contributions).

## Verification

### Build

Formal reproduction requires elan, the pinned Lean and Mathlib dependencies, Python 3.11 or later, and GNU `timeout` (coreutils). Census reproduction additionally requires a C compiler and nauty 2.9.3. From the collection root:

```bash
python3 scripts/check.py --problem 585 --mode docs
python3 scripts/check.py --problem 585 --mode full
```

The documentation mode checks metadata and links. Full mode runs the package checks, configured module builds, statement/axiom audit, registered whole-file oracles and kernel replays. Download the pinned Mathlib cache first from `problems/585/` with `lake exe cache get`.

Current verification inventory: 78 registered declarations, 77 whole-file oracle checks, 438 configured custom modules.

Registered proved results use only `propext`, `Classical.choice` and `Quot.sound`. Each applicable `check.sh` must report `RESULT: PASS`. One registered declaration in `Openmath/Target.lean` has statement/axiom and kernel evidence but no whole-file oracle because the file also contains unproved conjectures. No registered proved result depends on `sorryAx`. See the [verification guide](../../docs/verification.md) and [dated v0.4.1 record](findings/V0.4.1.md#reproduction-and-responsibility). These checks do not regenerate the full finite census or establish novelty or human review.

## Citation and corrections

Use the [problem citation](CITATION.cff) and identify the exact declaration or source file. The package is Apache-2.0 with its [license](LICENSE) and [notices](NOTICE). For corrections, prior-work references or help reviewing a proof, see the [contribution guide](../../CONTRIBUTING.md).
