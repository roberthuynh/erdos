# Sources and attribution

## Mathematical sources

- [Erdős problem #1017](https://www.erdosproblems.com/1017) states the original integral estimation problem. The fractional results in this package do not solve that problem in full.
- József Balogh and Michael C. Wigal, [Packing edge disjoint cliques in graphs](https://arxiv.org/abs/2502.16683v2), arXiv:2502.16683v2 (2025). This supplies a packing comparison. A direct packing consequence is a specific comparison, not an exhaustive analysis of every use of the paper's methods.
- Adam Blumenthal, Bernard Lidický, Yanitsa Pehova, Florian Pfender, Oleg Pikhurko and Jan Volec, [Sharp bounds for decomposing graphs into edges and triangles](https://arxiv.org/abs/1909.11371v3), arXiv:1909.11371v3 (2020), Combinatorics, Probability and Computing 30 (2021), 271–287. This treats decompositions restricted to edges and triangles, with a different cost family.
- József Balogh, Jialin He, Robert A. Krueger, The Nguyen and Michael C. Wigal, [Clique covers and decompositions of cliques of graphs](https://arxiv.org/abs/2412.05522v3), arXiv:2412.05522v3 (2026), Advances in Combinatorics 2026:9. This provides the general fractional-cost framework and an external asymptotic rounding theorem. That rounding theorem is not a formal result of this package.

The graph reductions use the classical Zykov averaging framework: transfer weights between nonadjacent vertices, reduce positive support, and average the resulting exact demands on the unchanged graph. Split graphs, signed dual certificates and elementary subset counting also have classical antecedents. This package does not claim those general ideas originated here. Its finite statements and constructions are given in the result index and Lean sources; historical priority is not exhaustively established.

## Software dependencies

The [Lean theorem prover](https://github.com/leanprover/lean4), [mathlib](https://github.com/leanprover-community/mathlib4), and [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) supply the proof language, mathematical library and kernel-replay support. The exact revisions are recorded in [lake-manifest.json](lake-manifest.json). The package checks adapt the existing checks in this repository. Fetched dependencies retain their own licenses and notices.

## AI use

AI systems developed the mathematical arguments, formalizations and source reviews under Robert Huynh's direction. The manuscript is a new working exposition of the included results. No human mathematical review is claimed. AI systems are not named as coauthors. Formal verification addresses the precise Lean statements and does not establish novelty.
