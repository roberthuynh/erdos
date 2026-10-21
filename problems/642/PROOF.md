# Fifth-power density bound: argument and formal interfaces

This guide describes the earlier fifth-power theorem. The current cubic-logarithmic theorem is explained in the [working manuscript](manuscript/main.pdf) ([TeX source](manuscript/main.tex)).

## Statement and scope

There is an absolute constant C > 0 such that every finite simple graph G with n vertices and

$$
e(G)>Cn(\log(2n))^5
$$

has a simple cycle with at least as many distinct chords as vertices. A chord is an unordered edge of G with both endpoints on the cycle, excluding the edges used by the cycle. Logarithms are natural.

This document expands the composition and parameter argument of the supplied Lean proof. It gives written proofs of the scalar payment, probability intersection and deterministic retention steps, and states the extraction and probabilistic estimates at their implemented interfaces. It does **not** provide an independent full written proof of the spectral extraction, forest occupation, smoothing and self-avoidance estimates. Those remain supplied by the formal source closure. Thus it is an expert-readable guide to that proof, not a replacement for the 134-module source closure of that earlier theorem or a claim of human validation. Formal verification status is recorded separately in [VERIFICATION.md](VERIFICATION.md).

## 1. Contradiction and extraction

Call a graph *avoiding* if it has no cycle of the stated kind. This property passes to any graph admitting an injective graph homomorphism into it: a simple cycle maps to a simple cycle of the same length, and each chord maps to a distinct chord. Injectivity prevents a nonconsecutive pair from becoming consecutive. Additional edges in the receiving graph cannot destroy these chords. This transfer is implemented in `AvoidanceHeredity.lean`.

Write D = 2e(G)/n and L = log n. For sufficiently large n and D above an absolute multiple of L², `SpectralExtraction.exists_spectral_host` returns an actual graph H, injectively embedded into G, with order N and minimum degree d satisfying

$$
3\le N\le n,\qquad d\ge {D\over400L},\qquad
\Delta(H)\le100d,\qquad \gamma={b\over L^2},
$$

where b > 0 is absolute and b ≤ 1. H is connected and bipartite and has the implemented bipartite spectral gap γ. Regularization first selects a possibly noninduced subgraph; subsequent cut extraction takes an induced graph inside that subgraph. The composition retains an injective map to G. None of these properties is assumed of G. If G is avoiding, H is avoiding too.

**Supplier boundary.** The degree retention and spectral gap are conclusions of `RegularizationAssembly`, `CutExtraction` and `ExtractParameters`, composed in `SpectralExtraction`. Their complete analytic proofs are in those imports; they are not reproved in this document.

## 2. An independent avoidance bound and local fourth returns

The argument needs an all-graph avoidance estimate

$$
e(J)\le C_0|J|(\log(2|J|))^8                         \tag{P8}
$$

for every avoiding finite simple graph J. The source does not assume the final fifth-power theorem to get it. `InitialDensity.exists_eventual_avoiding_average_six` first combines extraction with the **earlier spectral host theorem** and its old parameter payment to obtain an eventual sixth-power average-degree bound. It weakens exponent six to eight and uses `AllOrdersDensity` to cover small orders. This proves `exists_initial_density`, the exact all-graph P8 predicate used below. The older route has no dependency on the new moment-host conclusion. The word “published” in the predicate's historical source comment does not make an external paper an axiom of this proof.

Applied to H, P8 and the handshaking identity give

$$
d\le {2e(H)\over N}\le2C_0(\log(2N))^8.             \tag{1}
$$

There is also a local use of P8. Let P be the transition matrix of ordinary simple random walk on H, with its actual vertex-degree denominators. For a vertex v, let c(v,w) count common neighbors, and put

$$
a=1+C_0\{\log(2(\Delta+\Delta^2))\}^8.
$$

For each integer j ≥ 1, the off-diagonal codegree threshold set S_j = {w ≠ v : c(v,w) ≥ j} satisfies

$$
j|S_j|\le a\{\deg(v)+|S_j|\}.
$$

Bipartiteness makes the neighbors of v disjoint from S_j. The incidence graph connecting these two sets therefore embeds injectively into H and is an avoiding subgraph, with order at most Δ + Δ². P8 bounds its actual edge count; each member of S_j contributes at least j incidences. `LocalCodegreeSubgraph` supplies the incidence graph and avoidance transfer. Combining these threshold bounds with the mass bound ∑_{w≠v}c(v,w) ≤ deg(v)Δ, the finite layer-cake estimate gives

$$
\sum_{w\ne v}c(v,w)^2\le8a\Delta^2.
$$

Expanding four random-walk steps and bounding each degree denominator below by d gives the implemented estimate

$$
P^4(v,v)\le {1\over d^2}+{8a\Delta^2\over d^4}.
$$

The diagonal term is treated separately in `FourthReturnExpansion`; this is not an assertion that all closed walks have identical weights. Since Δ ≤ 100d and d ≥ 1, `LocalAvoidanceMomentNormalized` proves, uniformly in v,

$$
P^4(v,v)\le{\Lambda\over d^2},\qquad
1\le\Lambda\le C_1(\log(2d))^8.                     \tag{2}
$$

Here C₁ is absolute once C₀ is fixed. The layer-cake inequality and incidence construction are formal suppliers; the displayed normalization follows by Δ² ≤ 10000d² and log(2(Δ+Δ²)) ≤ (2 + log(10100)/log 2)log(2d).

## 3. Host criterion and one common path

Set z = log N and k = ⌈2 + z/γ⌉. The strong moment-host theorem requires the three simultaneous inequalities

$$
Akz\le d,\qquad A\Lambda kz\le d^2\gamma,
\qquad Ak^2z\le N,                                  \tag{3}
$$

with the fixed absolute constant A = 10^1000. Together with (2), bipartiteness, connectedness, degree ratio and gap, these are exactly `MomentRichPath.StrongMomentHostPremises`.

Here is the random-walk conclusion and how its events are combined. `MomentHostParameters` chooses a number q of blocks, T = qk and t = ⌊(T+1)/8⌋, with q comparable to a₀N/k² for a fixed small a₀ > 0. Its rounded inequalities ensure T ≥ 16, t ≥ 2, 8t ≤ T+1 and t ≥ T/16. A rounded forest bundle in H supplies weighted counts between two pairs of time windows of the same length-T walk: an outer pair in indices [0,t−1] and [6t,7t−1], and an inner pair in [2t,3t−1] and [3t,4t−1].

The forest occupation and smoothing suppliers show that each count is at least

$$
\theta={dt^2\over10^{24}N}\ge3T
$$

except on an event of probability at most

$$
\varepsilon=
 e^{-t/(2\cdot10^{35}z)}+
 e^{-\gamma t/(2\cdot10^{21})}+
 e^{-\gamma t/(8\cdot10^{14})}
 \le3e^{-12\beta q}.
$$

The moment self-avoidance supplier gives probability at least e^{-6βq} that the **full** length-T walk is self-avoiding; β > 0 is fixed. These statements hold for the graph chain started at the same vertex. Offset-window transfer embeds both estimates in the same length-T probability space. By the union bound, the probability of either count falling below 3T is at most 6e^{-12βq}. `MomentRarityParameters.strict_intersection` proves

$$
6e^{-12\beta q}<e^{-6\beta q}.
$$

Consequently the self-avoiding event cannot be contained in the union of the two bad-count events. The finite probability space contains a positive-weight path in their difference. This is one path with both lower counts, not two independently selected paths. `MomentRichPath.exists_moment_rich_path` implements precisely this subtraction argument.

**Supplier boundary.** The bounds on the two window events and on self-avoidance are substantial estimates. Their proofs are in `MomentTwoWindow`, `MomentSelfAvoidance` and their forest/smoothing imports. This document states their quantitative outputs and proves their logical intersection; it does not substitute a sketch for their full analytic proofs.

## 4. Weighted counts become actual retained chords

On a self-avoiding path, `windowWeightedCountAt_eq_pairEdgesAt_of_eq` identifies each weighted count with the cardinality of a finset of actual unordered selected forest edges. In particular there are sets O and I with |O|,|I| ≥ 3T. This equality is the bridge from weights to distinct edges; counting path occurrences alone would not suffice.

Choose an edge of O. Its endpoints have indices i < t and 6t ≤ j < 7t. Close the path segment from i to j using this edge. Because the full path is simple and j−i ≥ 2, the result is a simple cycle of length ℓ = j−i+1 ≤ T+1. Every edge of I has both endpoints between indices 2t and 4t−1, hence strictly inside this retained segment. Thus all |I| edges belong to the graph induced on the cycle vertices.

At most ℓ edges in that induced graph are cycle edges. Since T ≥ 16, 3T ≥ 2(T+1) ≥ 2ℓ. Therefore there are at least |I|−ℓ ≥ ℓ distinct chords. `SpectralCycleProof.rich_cycle_of_actual_window_counts` supplies the edge sets and closing indices; `FourIntervalCycle` checks the retained indices; `RichWalkCycle` and `CycleSupport` subtract cycle edges as finite sets. The outer edges are used only to find the closing edge, not added to the inner count. Mapping the resulting cycle through the injective homomorphism H → G preserves its length and distinct chords.

## 5. Why the original density exponent is five

It remains to pay (3) from D ≥ KL⁵, with one universal K. This is where both original order n and extracted order N matter. Let c = 1/400. Extraction gives d ≥ cD/L ≥ cKL⁴. For large enough n, L ≥ 1 and L log 3 ≥ 1. With z ≤ L and γ = b/L², rounding gives

$$
k\le4L^2z/b.
$$

The degree condition follows from Akz ≤ (4A/b)L⁴. For the moment and order conditions we use an elementary estimate valid for x ≥ 1:

$$
(\log(2x))^8\le Qx^{1/4},\qquad Q=2\cdot32^8.
$$

Indeed apply log r ≤ r−1 ≤ r to r = (2x)^{1/32}, raise to the eighth power, and use 2^{1/4} ≤ 2. Put P₀ = 2C₀Q and R = C₁Q. Equations (1) and (2) imply

$$
d^4\le P_0^4N,\qquad\Lambda\le Rd^{1/4}.            \tag{4}
$$

Choose M = 16A/b², W = 4AR/b² and B ≥ 1 + 4A/b + W + P₀M; choose K = B/c. Then d ≥ BL⁴ pays the degree inequality. Writing u = d^{1/4}, we have u ≥ L and

$$
{A\Lambda kz\over\gamma}
 \le WL^6u
 \le BL^7u
 =(BL^4)uL^3
 \le du^4=d^2,
$$

which pays the moment inequality. For the order inequality, (4) and d ≥ BL⁴ ≥ P₀ML⁴ give

$$
N\ge(d/P_0)^4\ge M^4L^{16}\ge ML^7
 \ge Ak^2z.
$$

Thus N ≤ n is used to bound z, while a **lower** bound on N is obtained from avoidance, not assumed. Mere N ≤ n would not pay the order condition. All constants and the sufficiently-large-order cutoff are selected before n, N, D, d and Λ. These calculations are formalized in `StrongGlobalApplicability.exists_uniform_strong_applicability`.

The structural improvement exposed by this composition is use of the avoidance-derived fourth-return bound Λ/d² in the strengthened host criterion. The original graph loses one logarithmic power in extraction, leaving a retained degree of order L⁴ from D of order L⁵. The three inequalities above show why that retained degree suffices. This describes the mechanism in this package; it does not independently establish worldwide priority for the mechanism or exponent.

## 6. All orders, antecedents and remaining reading limits

The contradiction proves an eventual fifth-power average-degree bound for avoiding graphs. `AllOrdersDensity` absorbs finitely many smaller orders into the universal coefficient, using the elementary simple-graph edge bound and log(2n) ≥ log 2 for n ≥ 1; n = 0 is handled separately. The identity 2e(G) = nD converts average degree to edges with a constant factor. `OriginalBound` concludes the theorem with C quantified before the graph and order.

The published antecedent by Draganić, Methuku, Munhá Correia and Sudakov is the eighth-power edge threshold in *Cycles with many chords*, DOI 10.1002/rsa.21207. The extraction and random-walk approach belongs in that context. A public discussion sketch claims the seventh power; this package does not claim that exponent as new. Draganić and Girão's arXiv:2601.08769v1 gives Ω(ℓ/(log ℓ)^C) chords at constant minimum degree, a different tradeoff from retaining ℓ chords with a polylogarithmic global density requirement. See [SOURCES.md](SOURCES.md) for source versions and access limits. No fresh broad novelty search or full primary-paper audit was performed in preparing this exposition.

The written calculations above were checked against the supplied interfaces in `SpectralExtraction`, `InitialDensity`, `LocalAvoidanceMoment`, `LocalAvoidanceMomentNormalized`, `StrongGlobalApplicability`, `MomentHostParameters`, `MomentRichPath`, `MomentCycleProof`, `SpectralCycleProof`, `FourIntervalCycle` and `RichWalkCycle`. The underlying spectral, forest, layer-cake, occupation and smoothing supplier proofs have not all been independently expanded or audited here. The full formal closure, fresh kernel checking, statement fidelity, mathematical novelty and human review remain separate judgments. The theorem gives a partial density improvement, not the original linear bound and not a log-log refinement.
