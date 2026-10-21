# Results

Write n = |V(G)| and e = |E(G)|. An exact fractional edge-clique partition assigns nonnegative mass to actual cliques of order at least two, with load exactly one on each original edge. Its cost is the sum of its masses. An integral partition partitions those same edges into cliques. All graphs below are finite and simple.

## Density-dependent upper bound

Every graph admits an exact fractional partition P with

`P.cost + (√7/3)e ≤ (1 + √7/3)n²/4`.

The theorem includes empty graphs and arbitrary vertex types. It imposes no restriction on clique size or edge density. It does not assert an integral partition at this cost.

Declaration: `Erdos1017.sharp_affine` in [SharpAffine.lean](Erdos1017/SharpAffine.lean). Definitions: [Basic.lean](Erdos1017/Basic.lean).

## Finite lower construction

For natural n,m satisfying n ≥ 100, 2n ≤ m and 100m ≤ n², put q = ⌊n²/4⌋. There exists a graph of order exactly n with exactly q + m original edges such that every exact fractional partition and every integral partition has cost at least

`q − m + 2m²/(9n²) − 8m/(9n) − 29/18`.

The same graph works for both conclusions, and an integral partition exists. The signed certificate requires exact loads. This lower bound is not asserted for fractional covers with loads merely at least one.

Declaration: `Erdos1017.Mesoscopic.finite_lower_bound` in [MesoscopicLower.lean](Erdos1017/MesoscopicLower.lean). The lower bound uses real subtraction; q is a natural floor.

## Exact binomial-cost extremum

For natural n and t ≥ 2, let `M_t(n) = max_{0 ≤ a ≤ n} a binom(n − a, t − 1)`. This is zero at n = 0; for positive n the maximum can equivalently run from 1 to n.

A j-clique has cost `binom(j − 1, t − 1)`, with cost zero for j < t. Every original t-clique must receive load exactly one for a decomposition, or at least one for a cover. Every graph of order n admits a fractional decomposition of cost at most M_t(n). A split graph with n vertices has a decomposition of cost exactly M_t(n), and every fractional cover of that graph costs at least M_t(n). Thus the two global fractional extrema agree, including n < t.

Declaration: `Erdos1017.Binomial.exact_fractional_extremum` in [BinomialSharp.lean](Erdos1017/BinomialSharp.lean). Definitions: [BinomialDefs.lean](Erdos1017/BinomialDefs.lean). This cost differs from unit-cost edge partitions even when t = 2.

## Larger-slope obstruction

For every real λ > √7/3, there exists a finite split graph G such that every exact fractional partition P satisfies

`(1 + λ)n²/4 < P.cost + λ e(G)`.

Together with the upper bound, this excludes any larger universal slope in this anchored affine form. It does not determine the entire extremal curve at each density.

Declaration: `Erdos1017.sharp_affine_slope_barrier` in [SlopeBarrier.lean](Erdos1017/SlopeBarrier.lean).

## Near-complete upper bound

Every finite simple graph admits an exact fractional partition P satisfying `P.cost + 2e(G) ≤ n²`. This is a second upper bound; no integral conversion is part of the declaration.

Declaration: `Erdos1017.Dense.near_complete` in [NearComplete.lean](Erdos1017/NearComplete.lean).

## Supporting results

The [proof map](PROOF-MAP.md) identifies the supporting results included in the complete source closures. The finite selector laws, graph lifts, weighted reductions, trade identities, rational enclosures, signed duals and interpolation lemmas retain their own hypotheses. They are not additional claims that the original integral problem is solved.
