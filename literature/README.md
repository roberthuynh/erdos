# Prior work and references

This note records prior work related to the repository, including the v0.4 additions. It provides attribution and comparisons, without claiming a complete literature search or priority clearance. A quartic here means a nonempty 4-regular subgraph.

The comparisons below use named published works and deliberately public preprints. They do
not establish worldwide novelty, priority, or a complete exclusion of classical methods.

## Comparisons for the v0.4 additions

The [v0.4 mathematical note](../findings/V0.4.md) states the exact degree caps, orders,
edge counts and existential support conclusions. The following is a bounded comparison with
named public sources. It does not establish priority or the absence of an older theorem.

| Result or method | Public source inspected | What the comparison does and does not establish |
|---|---|---|
| Parameterized large-degree existence | AFK (1984), Remark 3.6, printed p.85 | Write t=(q−1)n−e(G). For a finite simple bipartite graph with n≥2q and maximum degree at most 2q−2, a nonempty q-regular subgraph exists for integer h≥6, q≥4096(h+1)^2 and t≤hq−16h². No selected support, balance or minimum degree is required from the caller. The conclusion alone supplies neither a cycle pair nor an improvement to the Erdős 585 bound. |
| Final large-degree bipartite existence | AFK (1984), Remark 3.6, printed p.85 | The final theorem assumes q≥2^18, n≥2q and maximum degree at most 2q−2, and allows t≤q^(3/2)/128. It produces a nonempty original q-regular subgraph. AFK's prime-power route allows t≤q−2. On that overlap, the exact difference is floor(q^(3/2)/128)−q+2 edges, equal to 786434 at q=2^18. This compares one named route, not all prior work. |
| Other guarded extraction statements | Pyber–Rödl–Szemerédi (1995), Lemma 2.1, printed p.46; Hao–Li–Yu (2025), Theorem 1.6 | PRS requires prime-power Q≥q, maximum degree at least 2Q−1 and a strict average-degree inequality. That degree guard fails at cap 2q−2. Hao–Li–Yu is a separate paper from Fan–Lin and imposes balance, minimum degree and edge-count conditions not supplied uniformly here. These are direct-statement comparisons, not exclusions of adaptations. |
| Classical factor and cut criteria | Fan–Lin, arXiv:2211.09304v1, Lemma 3.1 (crediting Ore); Enomoto–Ota–Kano (1988), Lemma 4 | Fixed-support factor feasibility and local inequalities from minimal failing cuts are established ingredients. Whether the full support-selection and quantitative cut argument here has a classical derivation remains unresolved. No broadly new method or independently new second application is claimed. |
| Bipartite matching and prescribed degrees | Bahmanian, arXiv:2203.12470v1, Introduction, Theorem 1.3 and Remark 1.5 | The prescribed-degree criterion and its Hall special case belong to established factor theory. A local proof that chooses a support or verifies all the required cuts must be explained separately. A Lean formalization of this machinery does not make it a new matching theorem. |
| Regular factors of vertex-deleted subgraphs | Egawa–Kimura (2022); Katerinis (2025), as cited in the findings | Spanning factors of degree at most half the host degree; the target q exceeds (2q − 2)/2, so these do not apply directly. Not an exclusion of adaptations. |
| Modular divisibility | Berthe et al., arXiv:2507.04254v2, Lemma 5 | If p(x) denotes the smallest prime at least x, the bound for avoiding a nonempty k-divisible subgraph is e≤(p(3k/2)−1)n, improved to e≤(p(k)−1)n for odd k. This does not supply a positive deficit allowance below (k−1)n. Divisibility after identifying split vertices is not automatically exact regularity on the original support. |
| Quartic extraction | Alon, Friedland and Kalai (1984), Remark 3.6, printed p.85 | For prime-power q = 4, their remark yields a nonempty 4-divisible subgraph in bipartite graphs above 3(n − 1) edges, hence a 4-regular one when the maximum degree is at most seven. The v0.4 result assumes maximum degree at most six and n ≥ 4 and uses 3n − 6 edges. This is a difference between these two statements, not a novelty conclusion. |
| Relation to the original problem | Chakraborti, Janzer, Methuku and Montgomery, *Edge-disjoint cycles with the same vertex set*, arXiv:2404.07190v1, Theorem 2 | This is the source of the polylogarithmic upper-bound context for Erdős 585. The regular-subgraph results in this update do not improve that bound. |
| Regular-subgraph extraction at general density | The same four authors, *Regular subgraphs at every density*, arXiv:2411.11785v2, Theorem 1.5 | This theorem supplies regular subgraphs from an average-degree condition. It does not supply a cycle decomposition. It is a different paper from the one proving the cycle-pair upper bound. |

A standard argument from König's theorem, that every regular bipartite multigraph decomposes into perfect matchings, gives the elementary allowance
t≤q−2 for every integer q≥2. The cap forces equal shores because t≥(q−1)|a−b|.
Completing to a (2q−2)-regular bipartite multigraph uses t auxiliary edges. Its perfect-matching
decomposition has at most t matchings containing added edges, leaving at least q clean
matchings and hence a spanning q-factor in the original graph. This all-integer argument is
not attributed to AFK's prime-power theorem. The [mathematical note](../findings/V0.4.md)
gives the derivation and explains why it does not automatically extend to the larger allowance.

Bermond and Las Vergnas's original Theorems 1 and 2 were checked at printed pp.10 and 12.
Their discrepancy, connectivity and parity conditions must be retained. With reference degree
2q−2, the total degree discrepancy is 2t. For even q the strict discrepancy budget in
Theorem 1 permits only t=0; for odd q Theorem 2 requires q≤(2q−2)/2, which fails.
Other reference degrees, selected supports and completion arguments have not been excluded.
The construction bounds in the mathematical note leave explicit gaps and do not establish sharpness.

AFK Theorem 4.3 has a lower degree guard and a strict average-degree inequality. The printed
Remark 4.8(b) omits a lower degree guard and has an applicability ambiguity; no comparison here
uses its unrestricted literal reading. Remark 4.8(a) announces an improvement without stating
its numerical value. A 'Thomassen 1999' citation carried in this project's earlier literature notes remains unidentified and is not used as a source here.
The original Olson pages and the specified passages of Bollobás's *Extremal Graph Theory*
(Chapter VII, Problem 23 and Problem 20 on p.399) remain reading limits. Original Hall, Ore and
Tutte papers were not newly read. Lovász's (g,f)-factor theorem, the structure of minimum-deficiency sets and the monograph literature on factors were not compared. These limits prevent an exhaustive prior-art claim.

The comparisons with CJMM's *Regular subgraphs at every density* use arXiv:2411.11785v2.
Theorem 1.13 gives target degrees up to c(λ)d for an existential constant. Its displayed choice
of constant does not certify the near-half-degree target here; this does not exclude sharper
constants or reductions. Jiang–Longbrake's arXiv:2507.03261v2 Theorems 1.3 and 1.5 give
almost-regular and almost-biregular outputs. Neither observation is a method-novelty proof.

For the prescribed-degree comparison, Theorem 1.13 of [arXiv:2411.11785v2](https://arxiv.org/html/2411.11785v2#S1.Thm13) guarantees every integer target degree r ≤ c(λ)d under Δ ≤ λd. The same statement appears as Theorem 1.13 in the [author-hosted manuscript](https://rhmontgomery.warwick.ac.uk/papers/37regularsubgraphs.pdf), printed p.3. For the v0.4 host, d = 2q − 2 − 2D/n. Its headline assumptions imply 2q − 2 − √q/128 ≤ d ≤ 2q − 2. At q = 262144 this gives d ≥ 524282 and q/d ≤ 131072/262141. Applying that source directly to target degree q requires q ≤ c(λ)d. The displayed proof gives a conservative admissible constant, not an upper bound on every possible constant; it does not settle whether an optimized or specialized argument implies this case. No novelty conclusion follows.

The CJMM publication venues and years were checked against
[Richard Montgomery's author bibliography](https://rhmontgomery.warwick.ac.uk/papers.html).
The preprint theorem numbers in the comparisons refer to the stated arXiv versions. For
*Edge-disjoint cycles with the same vertex set*, the published Theorem 1.2 on printed p.3
was also checked separately. Journal-version numbering for *Regular subgraphs at every
density* and the remaining pagination entries were not newly checked in this pass.

## Comparisons for v0.3 and earlier

These comparisons concern the results public since v0.3. QB(5) concerns finite simple bipartite graphs with n ≥ 3, maximum degree at most six and at least 3n − 5 edges.

| Topic | Earlier mathematics | Scope of this repository's comparison |
|---|---|---|
| Quartic extraction | Alon, Friedland and Kalai, *Regular subgraphs of almost regular graphs* (1984), Remark 3.6: bipartite hosts of maximum degree at most seven at 3n−2 edges | QB(5) has a maximum-degree-six hypothesis and 3n−5 threshold. The earlier remark does not directly give that threshold. Both statements conclude quartic extraction; neither asserts a Hamiltonian decomposition or a cycle pair. |
| Five-regular obstructions | Read and Wilson, *An Atlas of Graphs* (1998), Chapter 5, p.155 | Generic five-regular graphs without a quartic are already recorded. Exact witness orders, bipartite restrictions and minimum-order census claims require additional comparison and evidence. |
| Small values | [Erdős Problem a Day](https://erdosproblemaday.com/report/585), July 28, 2026, Section 3 (read October 8, 2026) | Values through n = 10 were previously reported. Exact values are Lean-checked through n = 7; at n = 8, 9 and 10, upper exclusions are computational. The entries f(11) = 31 and f(12) = 36 already appear in v0.3 and extend that report. |
| Zero-sum selection | AFK Theorem 2.1 credits Olson's finite abelian zero-sum theorem; Alon's *Tools from Higher Algebra*, Theorem 6.2, gives an inspected statement and proof | Original Olson pages remain an access gap. The selection principle is prior mathematics, even when found independently in this project. |
| Twin/Euler lift | Eppstein, *Hamiltonian Cycles in Subdivided Doubles*, arXiv:2510.18359v1, Theorems 1 and 2 | The subdivided-double Hamilton lift is known. Any actual-host density application needs its separate embedding and selection hypotheses. |
| Sidon palettes | Huang, Tait and Won, *Sidon sets and 2-caps in F_3^n* (2019), Theorems 3.2 and 3.4; Cilleruelo's Example 1 (arXiv:1003.3576v2, 2011) | Sidon/2-cap equivalence and the parabola construction are prior geometry. The proposed contribution is its specific recoloring-detector application. |
| Haar decompositions | Bermond, Favaron and Mahéo (1989), Main Theorem, for connected quartic abelian Cayley graphs; Zhou et al., arXiv:1810.07866v1, Theorem 3, for the stated prime dihedral case | These cover specified identified Haar cases. They do not establish a new general Haar decomposition or automatically cover every nonsymmetric or composite template. |

Alejandro Zarzuelo Urdiales's *Robert: eight-family novelty and current proof scope* and *Five-family primary-literature comparison*, both dated October 7, 2026, informed these literature and proof-coverage comparisons. This credit identifies that comparison work; it does not establish human verification of this repository's proofs. Those two documents are in his public review repository ([alejandrozu/openmath-2026-judging](https://github.com/alejandrozu/openmath-2026-judging/tree/main/robert-review-2026-10-07/research), files `Robert8_current_novelty_and_proof_scope.md` and `research_five_comparison_matrix.md`), not in this repository.

## References

The references below support the comparisons above and the existing public findings. [REFERENCES.json](REFERENCES.json) supplies the same bibliographic data in machine-readable form.

The October 11 comparison, carried out by AI agents, checked AFK pp.85–87, PRS p.46 and Bermond–Las Vergnas's original
statement pages against images. The original Enomoto–Ota–Kano paper was read for selected statement and method
comparisons, without independent validation of their complete proofs. Original-source reading, a formal proof check, novelty assessment, publication
and outside expert endorsement are separate claims. No outside expert endorsement is asserted.

- Noga Alon, Shmuel Friedland, Gil Kalai. [*Regular subgraphs of almost regular graphs*](https://web.math.princeton.edu/~nalon/PDFS/Publications/Regular%20subgraphs%20of%20almost%20regular%20graphs.pdf). JCTB 37 (1984), 79–91. Theorem 2.1 (Olson); Corollary 2.2; Theorem 3.1; Remark 3.6.

- Debsoumya Chakraborti, Oliver Janzer, Abhishek Methuku, Richard Montgomery. [*Edge-disjoint cycles with the same vertex set*](https://arxiv.org/abs/2404.07190). Advances in Mathematics 469 (2025), 110228. Inspected arXiv:2404.07190v1: Problem 1; Theorem 2. Separately inspected published version: Theorem 1.2, printed p.3.

- Oliver Janzer, Benny Sudakov. [*Resolution of the Erdős–Sauer problem on regular subgraphs*](https://arxiv.org/abs/2204.12455). Forum of Mathematics, Pi 11 (2023), e19. Main fixed-degree theorem.

- Jean-Claude Bermond, Odile Favaron, Maryvonne Mahéo. [*Hamiltonian decomposition of Cayley graphs of degree 4*](https://hal.inria.fr/hal-02500476/file/67-BFM89-hamilton-cayley-degree4.pdf). JCTB 46(2) (1989), 142–153. Unnumbered Main Theorem.

- Yixuan Huang, Michael Tait, Robert Won. [*Sidon sets and 2-caps in F_3^n*](https://msp.org/involve/2019/12-6/involve-v12-n6-p06-p.pdf). Involve 12(6) (2019), 995–1003. Theorems 3.2 and 3.4; following parabola claim.

- David Eppstein. [*Hamiltonian Cycles in Subdivided Doubles*](https://arxiv.org/abs/2510.18359). Ars Mathematica Contemporanea 26 (4.02) (2026), 1–9; arXiv:2510.18359v1 (2025). Definitions 1–2; Theorems 1 and 2.

- Ronald C. Read, Robin J. Wilson. [*An Atlas of Graphs*](https://oeis.org/A000088/a000088_14.pdf). Oxford University Press (1998). Chapter 5, printed p.155; Theorem 11.

- John E. Olson. [*A combinatorial problem on finite Abelian groups, I*](https://doi.org/10.1016/0022-314X(69)90021-3). Journal of Number Theory 1(1) (1969), 8–10. Original theorem number unverified. The original full text was unavailable for this comparison. AFK Theorem 2.1 credits Olson; Alon's Tools from Higher Algebra, Theorem 6.2, gives the inspected statement and proof.

- Hui Zhou, Liufeng Xu, Yang Cui, Qi Ding, Yanfeng Luo, Xing Gao, Dong Yang. [*Hamiltonian decomposition of the Cayley graph on the dihedral group D_{2p} where p is a prime*](https://arxiv.org/abs/1810.07866v1). arXiv:1810.07866v1 (18 October 2018). Theorem 3; Lemma 5.

- Noga Alon. [*Tools from Higher Algebra*](https://web.math.princeton.edu/~nalon/PDFS/tools1.pdf). Author-hosted chapter; publication year and venue unverified in this comparison. Theorem 6.2 and its full group-ring proof. The citation identifies the author-hosted chapter; its publication year and venue have not been established in this comparison.

- Debsoumya Chakraborti, Oliver Janzer, Abhishek Methuku, Richard Montgomery. [*Regular subgraphs at every density*](https://doi.org/10.1090/tran/9694). Transactions of the AMS 379 (2026), 8069–8090; DOI 10.1090/tran/9694. [Inspected preprint v2](https://arxiv.org/abs/2411.11785v2), Theorems 1.4, 1.5 and 1.13. The listed theorem numbers refer to preprint v2; published numbering has not been independently compared.

- Javier Cilleruelo. [*Combinatorial problems in finite fields and Sidon sets*](https://arxiv.org/abs/1003.3576). Inspected preprint arXiv:1003.3576v2 (2011). Example 1.

- Patrick White; site discloses Claude (Anthropic) assistance. [*Erdős problem #585: live audit and exact small cases*](https://erdosproblemaday.com/report/585). Erdős Problem a Day working report, July 28, 2026. Section 3, table through n = 10. Working report; not a Lean proof or independent human review. Read October 8, 2026.

- Amin Bahmanian. [*On Factors with Prescribed Degrees in Bipartite Graphs*](https://arxiv.org/abs/2203.12470v1). Public preprint, arXiv:2203.12470v1 (March 23, 2022). Introduction; Theorem 1.3; Remark 1.5. Journal status was not established in this comparison. The inspected HTML displayed a later internal date; the citation is pinned to the arXiv version identifier.

- Jean-Claude Bermond and Michel Las Vergnas. [*Regular factors in nearly regular graphs*](https://doi.org/10.1016/0012-365X(84)90030-X). Discrete Mathematics 50 (1984), 9–13. Theorem 1, p.10; Theorem 2, p.12. Original statement pages 10 and 12 were visually checked by an AI agent on October 11; a full independent proof validation is not claimed.

The published version of Chakraborti, Janzer, Methuku and Montgomery, *Edge-disjoint cycles with the same vertex set*, was also inspected: [published primary text](https://infoscience.epfl.ch/server/api/core/bitstreams/c50802dc-ab11-4995-aa14-bc1f434d267d/content), Theorem 1.2, printed p.3. This is separate from the pinned arXiv:2404.07190v1 comparison above, whose labels are Problem 1 and Theorem 2. The published front matter gives Advances in Mathematics 469 (2025), 110228, DOI 10.1016/j.aim.2025.110228.

- László Pyber, Vojtěch Rödl, Endre Szemerédi. [*Dense Graphs without 3-Regular Subgraphs*](https://doi.org/10.1006/jctb.1995.1004). Journal of Combinatorial Theory, Series B 63 (1995), 41–54. Lemma 2.1, printed p.46. Original printed statement visually checked by an AI agent on October 11, 2026. It uses a strict average-degree inequality; the maximum-degree guard is at least 2Q−1.

- Dandan Fan, Huiqiu Lin. [*Spectral conditions for k-extendability and k-factors of bipartite graphs*](https://arxiv.org/abs/2211.09304v1). Inspected public preprint arXiv:2211.09304v1, November 17, 2022. Theorem 1.3; Lemma 3.1. Selected statements read October 11, 2026. No line-by-line published-version comparison. Distinct from Hao–Li–Yu (2025).

- Yifang Hao, Shuchao Li, Yuantian Yu. [*Bipartite binding number, k-factor and spectral radius of bipartite graphs*](https://doi.org/10.1016/j.disc.2025.114511). Discrete Mathematics 348(8) (August 2025), 114511. Theorem 1.6, cases (i)–(iii), and Theorem 1.7 in public introduction. Publisher public introduction directly read October 11, 2026, including Theorem 1.6 exceptions. Complete proof not read in this final comparison.

- Hikoe Enomoto, Katsuhiro Ota, Mikio Kano. [*A sufficient condition for a bipartite graph to have a k-factor*](https://doi.org/10.1002/jgt.3190120115). Journal of Graph Theory 12 (1988), 141–151. Theorems 1, 3 and 5; Lemmas C and 4; printed pp.143 and 147. Original statements and Lemma 4 inspected October 11, including a visual check of printed p.143. No full independent proof validation claimed.

- Gaétan Berthe, Marthe Bonamy, Fábio Botler, Gaia Carenini, Lucas Colucci, Arthur Dumas, Fatemeh Ghasemi, Pedro Mariano Viana Neto. [*On Modular Edge Colourings of Graphs*](https://arxiv.org/abs/2507.04254v2). Inspected public preprint arXiv:2507.04254v2, December 5, 2025; arXiv record reports accepted for publication in SIAM Journal on Discrete Mathematics. Lemma 5 and its proof. Version and status record checked October 11, 2026. Paper writes q(x) for the least prime at least x; page comparison renames this p(x) to avoid conflict with target degree q. No final journal-version comparison.

- Tao Jiang, Sean Longbrake. [*Regularization and asymmetric extremal numbers of subdivisions*](https://arxiv.org/abs/2507.03261v2). Inspected public preprint arXiv:2507.03261v2, July 16, 2025. Theorems 1.3 and 1.5; definitions of almost-regularity and almost-biregularity. Selected statements directly read October 11, 2026. Publication status not asserted.

- Béla Bollobás, Jeong Han Kim, Jacques Verstraëte. [*Regular Subgraphs of Random Graphs*](https://mathweb.ucsd.edu/~jverstra/regular.pdf). Inspected public author manuscript dated February 21, 2003; published Random Structures & Algorithms 29 (2006), 1–13. Proof of Theorem 2.2, printed pp.3–4: the classical capacity network used in the proof companion. This citation does not identify the project support-selection argument with the paper's random-host theorem. No full proof audit or line-by-line journal comparison.
