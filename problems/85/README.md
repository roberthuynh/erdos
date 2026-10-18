# Erdős Problem 85: projective-incidence repair

[Collection](../../README.md) · [Result index](RESULTS.md) · [Written proof](PROOF.md)

## The problem

For an integer m ≥ 4, let f(m) be the least integer such that every simple graph on m vertices with minimum degree at least f(m) contains a four-cycle. [Erdős #85](https://www.erdosproblems.com/85) asks whether f(m+1) ≥ f(m) for all sufficiently large m. A four-cycle need not be induced: extra edges are allowed.

**The original question remains open.** The result below concerns stability of finite projective incidence maps, a separate direction arising from the research. It gives no improvement to the original extremal bound. The [public discussion](https://www.erdosproblems.com/forum/thread/85) also asks about f(49); this package does not determine that value.

## Main results

**AI-reviewed written candidate. No Lean verification or human mathematical review. Public priority remains unresolved.**

The conclusion says that changing a small number of point and hyperplane assignments makes both maps agree with one exact coordinate embedding.

Let n ≥ 2, let q and r be arbitrary prime powers, and supply the canonical projective spaces PG(n,q) and PG(n,r). A point is a one-dimensional vector subspace; a hyperplane has vector dimension n. Take any fixed point map φ and hyperplane map ψ from the source space to the target space. Neither map is assumed injective or surjective.

Put N=(q^(n+1)−1)/(q−1), d=(q^n−1)/(q−1), and a=q^(n−1). There are N source points, N source hyperplanes and Nd incident point–hyperplane pairs, called flags. Let T count source flags (p,H) for which φ(p) does not lie in ψ(H), once each, and let δ=T/(Nd).

Let ρ be the fraction of all ordered source projective frames whose point images are target frames. A frame consists of n+2 points, every n+1 independent; repeated images fail this test.

If

    ρ > 0   and   δ ≤ ρ/(10^9 n²),

then there are an injective unital field homomorphism σ:F_q → F_r and A ∈ GL_(n+1)(F_r) such that the point map [v] ↦ [Aσ(v)], together with its coupled hyperplane map, differs from (φ,ψ) in at most

    D ≤ 5T/q^(n−1) ≤ 10T/d

source entries in total. The hyperplane image is the F_r-linear span of the embedded source hyperplane. The same σ and A serve both maps. In particular D/(2N) ≤ 5δ. This normalized bound follows from the displayed estimate; it is not an additional theorem or a converse equivalence.

The [proof](PROOF.md) gives the weighted chart transport and consistency argument. The [findings](FINDINGS.md) explain what the frame hypothesis excludes and why the maps must be corrected together.

## Status

This is one contribution family. Its plane specialization, collapse/survival dichotomy and incompatible-field consequence are refinements or corollaries, not separate breakthroughs. The theorem is existential: no efficient decoder or bit-complexity bound is claimed. Its small-error threshold is restrictive and is not shown sharp. It concerns equal finite projective dimensions and complete incidence data in canonical Desarguesian spaces, not arbitrary buildings or non-Desarguesian targets.

The written proof received separate AI correctness review during research. This establishes a review history, not mathematical certainty, human endorsement or formal verification. Older Lean results from the research do not verify this theorem and are not included as its dependencies.

## Prior work

The classical fundamental theorem of projective geometry supplies the semilinear model. Kollár, Lieblich, Olsson and Sawin give a probabilistic projective-geometry theorem for injective maps over a common finite field in dimension greater than three, measuring whole-line failures. This package supplies two arbitrary maps and measures individual point–hyperplane flags. A conversion between these inputs and error measures is not established here; no blanket strengthening is claimed.

Pankov and Vetterlein treat arbitrary maps preserving orthogonality in complex projective Hilbert space exactly. Arbitrary-map rigidity itself is therefore not claimed as new. The additive correction has classical BLR antecedents. The needed correction argument is proved in this package, not imported as an unexplained black box. See [sources and reading limits](SOURCES.md).

## Proofs and findings

[PROOF.md](PROOF.md) contains the complete written argument, including weighted plane correction, higher-rank containment, shared-pencil coherence, global reconstruction and paired repair. [RESULTS.md](RESULTS.md) identifies its statement and corollaries. [DEPENDENCIES.md](DEPENDENCIES.md) separates proof inputs from comparisons and historical predecessors. [FINDINGS.md](FINDINGS.md) gives a reader's guide and examples.

## AI use

AI agents produced the proof and this exposition. Separate fresh-context AI reviewers examined correctness and source comparisons during research; the release preparation also uses mathematical, community and frontier-lab reader perspectives. These are AI reviews, not human or institutional endorsements. See the [shared disclosure](../../README.md#ai-use). No personal account of the research is inferred from the agent records.

## Verification

From the collection root:

```bash
python3 scripts/check.py --problem 85 --mode docs
python3 scripts/check.py --problem 85 --mode full
```

For this written-only package both modes check document identities and local links. Full mode also exercises negative controls for those checks. Neither mode checks mathematical correctness. There is no Lean declaration, kernel replay or official theorem-oracle PASS for this result. See [verification details](VERIFICATION.md).

## Citation and corrections

Use [CITATION.cff](CITATION.cff) and identify the exact public Git commit and proof section. No DOI or public release version is assigned by this private preparation. Corrections and relevant public prior-work references should identify the exact statement, failed proof step or matching hypotheses; see [Contributing](../../CONTRIBUTING.md). Public wording and release remain the maintainer's decision.
