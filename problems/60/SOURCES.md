> AI-written exposition. The main result has [Lean verification](VERIFICATION.md); this does not certify every written intermediate statement. No human mathematical review is claimed.

# Published sources and formalization

## Written proof interfaces

Primary source: Jialin He, Jie Ma and Tianchi Yang, *Some Exact Results on 4-Cycles: Stability and Supersaturation*, CSIAM Transactions on Applied Mathematics 4 (2023), 74–128. [Published article](https://doi.org/10.4208/csiam-am.SO-2021-0006); [public preprint, arXiv:1912.00986v4, 28 January 2021](https://arxiv.org/abs/1912.00986v4). The published theorem numbering below is the interface used in this package; preprint numbering can differ.

- Theorem 2.1 (Metsch): for q≥3900, a 1-intersecting (q+1)-uniform hypergraph on exactly q²+q+1 points with more than q²−((sqrt(5)−1)/2)q+17sqrt(q/5) lines embeds in a projective plane of order q. Exact pairwise intersections are proved before this input is used.
- Lemma 2.1 (partial symmetry): a projective-plane incidence matrix symmetric in its rows and corresponding columns at at least q²−q+3 indices is wholly symmetric. The point-to-line bijection and cross-block symmetry are constructed before applying this input.
- §2.3 and Proposition 2.1: a simple polarity graph is C4-free, has degrees q or q+1 and at least q+1 absolute vertices; e(Q)=M−m_pi sqrt(q)/2 for an integer m_pi≥0, with e(Q)=M exactly for orthogonal polarities.
- Lemma 2.5: every nonedge ab has q−1, q, or q+1 simple length-three paths, edge-disjoint for this fixed pair; the count is q−1 exactly when both endpoints are absolute.
- Lemma 2.4: absolute vertices are independent. Proposition 2.2: for even q an orthogonal polarity has a degree-(q+1) nucleus adjacent to all absolute vertices.
- Theorem 1.1 and §2.3: for prime powers q≥14, ex(q²+q+1,C4)=M, and orthogonal polarity constructions exist. Used only for the powers-of-two interpretation and sharpness.

The elementary localization and completion arguments are supplied in this package. The localization ancestry is the same public preprint’s §8 and the earlier HMY argument; the completion ancestry includes Füredi’s incidence/symmetry method as cited by HMY. No third-party PDFs or copied source text are distributed. This list identifies mathematical dependencies; it is not a completed novelty or license-clearance report.

## Formal proof and Metsch attribution

The written proof cites the optimized embedding interface presented as Theorem 2.1 (Metsch) by He, Ma and Yang. The Lean proof instead proves the stronger-density specialization needed here, using an adaptation of the early finite-incidence arguments in Klaus Metsch, [*Linear Spaces with Few Lines*](https://doi.org/10.1007/BFb0083245), Lecture Notes in Mathematics 1490 (1991), especially §§3 and 6.2–6.7 and the §6.10 construction. At the present density, a unified deficit induction replaces the later optimized embedding branch. The restoration count is proved directly with the corrected factor t(n+2−t), rather than the printed t(n+1−t) in Lemma 3.8. The formal proof does not claim the full optimized embedding threshold.

The required partial symmetry, polarity, path-count and absolute-point consequences are proved in Lean. The powers-of-two ex=M statement is obtained from the universal lower bound and an explicit orthogonal-polarity construction. The full general Baer gap formula cited above is not a formalization claim. [Verification](VERIFICATION.md) identifies the final declarations and checks.

The published Metsch source was inspected for the selected dependency route; this is not a full-book review. Only original proof code and attribution are distributed here, not the book, extracted text or institutional-access material.
