# Results and exact statements

All graphs below are finite and simple. A rich cycle is a simple cycle whose number of distinct original chords is at least its length. Every whole-graph statement quantifies an absolute positive constant before the graph and its order. Every edge threshold is strict. At order zero, we define the whole edge threshold to be zero, matching the formal convention.

## Whole-graph bounds

Let $L=\log(2n)$ and $D(n)=\log\log(e^e+n)$. The following bounds each imply a rich cycle when the graph has more than the stated number of edges.

| Threshold | Formal declaration | Role |
|---|---|---|
| $CnL^3$ | `Erdos642.Log3V1_20261024.original_log3_rich_cycle` | Main theorem |
| $CnL^4$ | `Erdos642.Joint20261019.Original.original_joint_rich_cycle` | Earlier bound used for growth in the main proof |
| $CnL^5/D(n)$ | `Erdos642.Adaptive20261018.Original.original_adaptive_rich_cycle` | Earlier adaptive improvement |
| $CnL^5$ | `Erdos642.CampaignFe72210bContinuation3.OriginalBound.original_log_five_rich_cycle` | Previously published bound |

The constants in different rows need not coincide. The Lean definition of the adaptive threshold is `Erdos642.Adaptive20261018.AllOrders.psi`. Its denominator is at least one, including at order zero. For the cubic-logarithmic theorem, orders zero, one and two have an impossible edge antecedent after the constant is enlarged. No connectivity, bipartiteness or regularity hypothesis is imposed on the input graph.

## Supporting statements

These six named statements have exact-source checks and independent acceptance. Their scopes below are narrower than some possible generalizations. They do not improve the cubic-logarithmic threshold by themselves. The namespace prefix is `Erdos642.CloudT9_20261021`.

| Statement | Declaration after the prefix |
|---|---|
| If the disjoint parts $P,B$ cover a bipartite graph, then $e-3n=\sum_{p\in P}(\deg p-3)-3|B|$. | [ThreeLedger.three_ledger](Openmath/Erdos642/Proofs/CloudT9_20261021/ThreeLedger.lean) |
| A vertex of degree at most one does not lie on a simple cycle. | [PendantCycle.notMem_cycle_support_of_degree_le_one](Openmath/Erdos642/Proofs/CloudT9_20261021/PendantCycle.lean) |
| For one vertex $x$ of degree at most one, deleting its incident edges preserves the existence of a rich cycle. The vertex set is unchanged. | [PendantRich.hasRichCycle_deleteIncidenceSet_iff](Openmath/Erdos642/Proofs/CloudT9_20261021/PendantRich.lean) |
| For a simple cycle with vertex set $S$ in a bipartite graph with parts $P,B$, the cycle is rich exactly when $\sum_{b\in S\cap B}(|N(b)\cap S|-4)\ge0$. | [IncidenceLedger.rich_iff_ledger](Openmath/Erdos642/Proofs/CloudT9_20261021/IncidenceLedger.lean) |
| If $a,b,c\ne w$ lie in pairwise different components after deleting the vertex $w$, walks from $a$ to $b$ and from $b$ to $c$ share $w$ internally. | [TreeBranch.shared_internal_vertex_of_three_branches](Openmath/Erdos642/Proofs/CloudT9_20261021/TreeBranch.lean) |
| If $L>0$, $\ell=L^{1/4}$, $b=L/\ell$ and $d=bL$, then $d=L^{7/4}$. | [ExponentFixedPoint.d_eq_rpow](Openmath/Erdos642/Proofs/CloudT9_20261021/ExponentFixedPoint.lean) |

The last statement is an exact arithmetic identity under the displayed equalities. It does not prove asymptotic sampling hypotheses or a graph threshold with exponent $11/4$. The tree statement concerns two consecutive walks and three components. The deletion statement concerns one vertex and incident-edge deletion. No set-deletion theorem is claimed.

The package also includes the formal dependencies of these results. A dependency's inclusion does not make it a separately checked headline theorem or a new contribution. [VERIFICATION.md](VERIFICATION.md) distinguishes the previous source checks from the final package checks.
