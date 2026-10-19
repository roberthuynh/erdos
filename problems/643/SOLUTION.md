# A shadow and co-link bound for disjoint-union-free triple systems

Robert Huynh

[Manuscript](manuscript/main.tex) · [Sources](SOURCES.md) · [Combined proof](coefficient-one-design/README.md) · [Finite certificates](CERTIFICATES.md) · [Verification](VERIFICATION.md)

## Abstract

We present a computer-assisted proof that every finite $3$-uniform hypergraph $H$ with no four distinct edges $A,B,C,D$ satisfying $A\cap B=C\cap D=\varnothing$ and $A\cup B=C\cup D$ obeys
$2\vert H\vert \leq \vert \partial H\vert +\vert \operatorname{CL}(H)\vert$. Here $\partial H$ is its two-shadow and $\operatorname{CL}(H)$ consists of pairs of vertices having a nonempty common link. The inequality implies $\vert H\vert \leq\binom n2$ on $n$ vertices and, together with the classical star-plus-matching construction, the coefficient-$1$ asymptotic bound that answers the $t=3$ case of the asymptotic question of Erdős problem 643. The argument uses a fractional pair count, a structural description of negatively charged triples, and proportional redistribution through six-edge bicones. Its finite rational inequalities and their analytic reductions are stated explicitly. The main inequality, its finite and asymptotic consequences, and the classical design construction giving exact values at admissible orders have complete Lean verification with independent exact-source acceptance. AI systems developed and checked the proof and formalization; no human mathematical review has been completed. No new theorem for $t\geq4$ or classification of equality cases is asserted.

**Verification and review.** The exact main theorem and its source-stated corollaries have accepted complete Lean verification in the isolated proof project. The expanded supplementary source package passed its complete 126-module check, including general classical five-block design existence and exact extremal and forcing values at every admissible order. This formalizes a known construction; it is not a claim of new design-existence mathematics.

## The problem and result

The problem page [8](#reference-8) asks: “Estimate $f(n;t)$ – in particular, is it true that for $t\ge3$”

$$
f(n;t)=(1+o(1))\binom{n}{t-1}?
$$

The result below addresses only the $t=3$ specialization of this asymptotic question.
A $3$-graph is a set of three-element subsets of a finite vertex set $V$; edges have no multiplicity. Call it *avoiding* if it has no four distinct edges $A,B,C,D$ such that

$$
A\cap B=C\cap D=\varnothing,\qquad A\cup B=C\cup D.
$$

All edges in this condition are edges of the original host. There is no replacement of the configuration by equal degrees, by an intersection pattern in a quotient, or by an edge count alone.

**Theorem: Main result.**

For every finite avoiding $3$-graph $H$,

$$
2|H|\leq |\partial H|+|\operatorname{CL}(H)|.
$$

In particular, if $\vert V\vert =n$, then $\vert H\vert \leq\binom n2$.

The definitions of both pair sets appear below; each is a subset of $\binom V2$, even when they overlap. Consequently the final implication in the theorem divides the sum of two bounds $\binom n2$ by two. It does not require the pair sets to be disjoint.

Let $\operatorname{ex}_3(n)$ be the maximum size of an avoiding $3$-graph on a fixed $n$-vertex set. Let $f(n;3)$ be the least integer edge threshold forcing the forbidden configuration. With this convention,

$$
f(n;3)=\operatorname{ex}_3(n)+1.
$$

A threshold exceeding the total number of triples is understood vacuously. In particular, one must not identify the extremal maximum with the forcing threshold.

**Corollary: Consequences of the [main theorem](#the-problem-and-result).**

For all $n\geq0$, $\operatorname{ex}_3(n)\leq\binom n2$ and $f(n;3)\leq\binom n2+1$. For $n\geq1$, the classical star-plus-matching lower bound, cited rather than reproved here, gives

$$
\binom{n-1}{2}+\left\lfloor\frac{n-1}{3}\right\rfloor
 \leq\operatorname{ex}_3(n)\leq\binom n2.
$$

Thus $\operatorname{ex}_3(n)=(1+o(1))\binom n2$ and $f(n;3)=(1+o(1))\binom n2$ as $n\to\infty$.

For $n=0,1,2$, there are no triples and [the main inequality](#the-problem-and-result) reads $0\leq0$; no positive codegree denominator is evaluated. The extremal statement for $n=0$ is separate from the displayed lower construction, which requires a distinguished vertex. More generally all denominators in the proof occur only at nonempty links, actual options, donors, or active bicones, as specified below.

**Equality and scope.**
Whenever a Steiner system $S(2,5,n)$ exists, filling every block with its ten triples gives the classical construction in Example 1.3 of [1](#reference-1). Hanani's 1961 existence theorem [10, (7.10), pp. 378–380](#reference-10), completed by the 1965 note [11, p. 711](#reference-11), supplies these systems for $n\ge5$ with $n\equiv1,5\pmod{20}$; $n=1$ is handled separately by the empty family. Together with the verified upper bound and the cited existence theorem, this gives $f(n;3)=\binom n2+1$ at those orders. This is an existence claim; the argument does not classify every extremal host or settle every finite value. The stronger structural conjecture of Howard [6, Conjecture 3.6](#reference-6) is not established by this inequality. The paper concerns $t=3$ only. Appendix [Exact equality examples and a tight local branch](#exact-equality-examples-and-a-tight-local-branch) exhibits cone configurations attaining the shadow–co-link bound, so equality there is not restricted to $K_5$ unions.

## Conventions and the counting identity

For a vertex pair $p$, put

$$
L(p)=\{v:p\cup\{v\}\in H\},\quad k_p=|L(p)|,\quad
 \partial H=\{p:k_p>0\}.
$$

For distinct vertices $x,y$, define

$$
\operatorname{CN}(x,y)=\{P\in\tbinom V2:P\cap\{x,y\}=\varnothing,
       \ P\cup\{x\},P\cup\{y\}\in H\},
\quad s_{xy}=|\operatorname{CN}(x,y)|,
$$

$$
\operatorname{CL}(H)=\{\{x,y\}\in\tbinom V2:s_{xy}>0\}.
$$

Pairs such as $xy$ are unordered sets. Expressions such as $x+uv$ mean $\{x,u,v\}$, with the distinctness imposed by being an edge.

For $T\in H$, a pair $P\subset T$ has a unique opposite vertex $a_P\in T\setminus P$. Its *options* through $P$ are $q=\{a_P,z\}$ for $z\in L(P)\setminus\{a_P\}$. Every such option meets $T$ exactly in $a_P$ and has $P\in\operatorname{CN}(q)$, so $s_q\geq1$. Distinct pairs of $T$ cannot yield the same option. Set

$$
\sigma(T)=\sum_{P\in\binom T2}\frac1{k_P},\qquad
 \tau(T)=\sum_{q\text{ an option of }T}\frac1{2s_q},\qquad
 c(T)=\sigma(T)+\tau(T)-2.
$$

Call $T$ deficient if $c(T)<0$ and then put $\operatorname{def}(T)=-c(T)>0$. The exact identities, proved in detail in the appendix, are

$$
\sum_{T\in H}\sigma(T)=|\partial H|,\quad
 \sum_{T\in H}\tau(T)=|\operatorname{CL}(H)|,\quad
 \sum_{T\in H}c(T)=|\partial H|+|\operatorname{CL}(H)|-2|H|.
$$

For the second identity an option $q$ belongs to exactly $2s_q$ distinct triples, not merely at most that many. This exact multiplicity is essential.

**Slots.**
Fix $T=abc$. Its groups are $A=L(bc)\setminus\{a\}$, $B=L(ca)\setminus\{b\}$ and $C=L(ab)\setminus\{c\}$. A slot is $(z,X)$ with $z\in X$: a vertex belonging to two groups has two distinct slots. Relations $R_b$ between $C,A$, $R_c$ between $A,B$, and $R_a$ between $B,C$ are defined by the triples $bxz$, $czy$, and $ayx$, respectively, with unequal slot vertices. A slot is isolated if it has no relation neighbour, type 1 if its neighbours lie in just one relation, and type 2 if they lie in both. Write $d(s)$ for its total relation degree and $\operatorname{cost}(s)=1/(2(1+d(s)))$. Avoidance forces every common link to be intersecting and every type 2 slot to have one neighbour in each relation, represented by the same vertex.

**Bicones.**
A common link is triangular when $\operatorname{CN}(x,y)=\{uv,vw,uw\}$ for distinct $u,v,w$. Its bicone $B_q$, $q=xy$, consists of the six triples $x+uv,x+vw,x+uw,y+uv,y+vw,y+uw$. The vertices $x,y$ are its apexes. A triple belongs to $B_q$ precisely when $q$ is one of its triangle options. Write $t_2(T)$ for the number of these options.
An apex-base pair is light if its codegree is two, heavy otherwise. A triple is exactly-one-light if exactly one of its two apex-base pairs is light. An apex with two such triples has a third triple, its anchor. The anchor is both-light or both-heavy. A bicone is active if it contains a deficient triple; $D_q$ is the set of those triples, $d_x$ counts them at apex $x$, and $\operatorname{act}(T)$ counts active bicones containing $T$.

## Proof architecture and the final implication

**Notation dictionary.**
The host quantities $k_p,s_q,\sigma,\tau,c$ and $\Phi=2\vert H\vert -\vert \partial H\vert -\vert \operatorname{CL}(H)\vert$ are fixed throughout. The unadorned groups $A,B,C$ are slots around a generic triple; $\mathcal A,\mathcal B,\mathcal C$ are slots around the anchor in setting S. In that setting $S_i=c(T_i)+13/12$, $D$ is the total deficit at the chosen apex, and $U,W$ collect the two sides of the anchor charge. The counts $j,d,e,r,k$ are defined in subdivisions 7.3 and 7.7; $m,m',n_B,n_C$ and $X$ in subdivision 8.1. A prime exchanges the $u$ and $w$ sides. The functions $g$ of Lemma 3g, $g_{10}$ of Lemma S10.1, and $g_W$ of Lemma W are different functions. Every cost uses the degree of a slot, so repeated outside vertices remain distinct when they occupy different groups.
The local inequality $c(T)\geq0$ is not an input. The proof allows deficient triples and establishes a global redistribution. The dependencies are:

| Stage | Required mathematical conclusion |
| --- | --- |
| Common links and slots | Intersecting common links; $s_q=1+d(s)$; type 2 slots are precisely triangle options. |
| Profile inequalities | $\sigma+\tau\geq23/12$, and every deficient triple satisfies the structural theorem G1. |
| Deficient-triple structure | Exactly one triangle option, exactly one light apex-base pair, and the specified common-link size two. |
| Anchor estimates | Both-light anchors supply at least $1/6$; both-heavy anchors supply the total deficit at their apex after division by their number of active bicones. |
| Conservation | Proportional distribution of each bicone pot makes every final charge nonnegative without changing its total. |

The analytic profile reduction separates no large relation, one large relation, and at least two large relations. It reduces only the first two branches to finite rational certificates; it does not infer a universal statement from small-host sampling. For both-heavy anchors the exhaustive branches are $d_x=2$; $d_x=1$ with no additional type 2 slot; and $d_x=1$ with an additional type 2 slot. The final branch splits by the count $m=0,1,$ or $m\geq2$ on the deficient side. An apparent mutual-partner branch is excluded by two disjoint pairs in a common link.

**The redistribution.**
A donor $T'$ has $c(T')>0$ and $\operatorname{act}(T')\geq1$. It sends $c(T')/\operatorname{act}(T')$ to each active bicone containing it. Write $\operatorname{pot}(q)$ for the total sent to $B_q$. Each $T\in D_q$ receives

$$
\operatorname{pot}(q)\frac{\operatorname{def}(T)}{\sum_{S\in D_q}\operatorname{def}(S)}.
$$

The denominator is positive because the bicone is active. This is a proportional split, not an equal split. Each donor sends exactly its charge, each pot is fully distributed, and only deficient triples receive. Thus the total charge is conserved.

G1 puts a deficient triple in exactly one active bicone. At either apex with $d_x>0$, parity leaves at most two deficient triples and a nondeficient anchor $A_x$. For a both-light anchor, its charge is at least $1/6$, it has exactly one triangle option, and each deficit is at most $1/12$. For a both-heavy anchor, the detailed estimates prove

$$
c(A_x)-\operatorname{act}(A_x)\sum_{T\in D_q,\ x\in T}\operatorname{def}(T)>\frac1{k_{uw}}>0.
$$

If both apexes have positive deficit, their anchors are distinct because each contains its own apex but not the other. Summing the anchor contributions over apexes with positive deficit therefore gives

$$
\operatorname{pot}(q)\geq\sum_{S\in D_q}\operatorname{def}(S).
$$

Every deficient triple receives at least its deficit; every other triple has nonnegative final charge. The conserved total is consequently nonnegative, giving [the main inequality](#the-problem-and-result). This last implication is conditional on the full local estimates, including the finite certificates, the six relabellings in Lemma S8(b), and the exceptional-slot inequality in Lemma S10.

## Relation to earlier work

Erdős discussed the distinct-union problem in [9, Section II, item 6](#reference-9). Füredi [1, Conjecture 1.4](#reference-1) conjectured the coefficient-$1$ upper bound
for sufficiently large $n$ and gave both the star-plus-matching lower
bound and the $K_5$-filled Steiner-system construction.
Pikhurko and Verstraëte [3, Theorem 2](#reference-3) proved
$\operatorname{ex}_3(n)\leq(13/9)\binom n2$ for every $n\geq1$.
The elementary common-link observation is related to their diagonal analysis: the proof of Lemma 9 excludes disjoint common-link pairs, while Lemmas 5–6 describe the triangle case. We prove the exact form used here directly.
Frankl and Füredi's pair-counting argument [2, Section 2](#reference-2)
provides a related precedent under the stronger weakly union-free hypothesis, which forbids equal unions of any four distinct triples without requiring paired edges to be disjoint. Their Theorem 1.6 gives $n(n-1)/3$ under that stronger hypothesis.
Mubayi [4](#reference-4) proved the coefficient-$1$ bound with the additional
forbidden configuration $K^{(3)}(1,2,4)$ in journal Theorem 1.3 (Theorem 1.4 in the author manuscript dated 11 June 2005).
The theorem here has no such additional hypothesis.
Huang, Ma and Yang [5, Theorem 1.2](#reference-5) establish the exact conjecture
for each fixed $r\geq4$ and sufficiently large $n$, while their
Section 7 leaves $r=3$ open. Their higher-uniformity result is separate
from the argument in this paper.

The theorem supplies the t=3 case of the asymptotic question in Erdős Problem 643. Huang, Ma and Yang's [versioned preprint, Theorem 1.2](https://arxiv.org/html/2609.37744v1) supplies the cases of every fixed t≥4 for sufficiently large n, with an order threshold depending on t. Taken together, these results give an affirmative answer to the asymptotic question for every fixed t≥3. The higher-uniformity cases rely on that external preprint and are not Lean-verified here; the Lean verification supplied here covers our triple theorem and the stated triple design consequences. This does not determine every finite extremal value or classify all triple equality cases.

The same research programme previously released a Lean-checked $4/3$ bound at public commit [74a2dc52](https://github.com/roberthuynh/erdos/commit/74a2dc52). The $9/8$ and $24/23$ bounds have separately recorded Lean checks; neither is the coefficient-one theorem or presented here as external published literature. The all-$n$ coefficient-one assertion is stronger than the sufficiently-large-$n$ form of Füredi's conjecture for triples.

Howard's thesis [6, printed p. 9](#reference-6) records the design-only classification of Dukes and Ling [7](#reference-7): simple disjoint-union-free designs with triple blocks and pair multiplicity three have the five-block construction. That prescribed-multiplicity result is distinct from classifying every extremal triple system. The six-page Dukes–Ling article itself was not obtained; this attribution uses the actually read thesis passage.

The attribution of classical five-block design existence to Hanani follows Füredi's Example 1.3 and the introduction of Pikhurko and Verstraëte. The original Hanani papers were subsequently obtained and visually read: all 26 pages of the 1961 paper and the complete one-page 1965 note. The 1961 statement (7.10), on page 378, retains a possible 141-point exception; the 1965 note supplies that case and explicitly removes the exception. This reading did not independently revalidate every finite table or block entry, or formally audit the historical proofs. The accompanying constructive Lean proof supplies its separate mathematical evidence and does not claim new design-existence mathematics.

The literature comparison is bounded by the sources and versions read. It establishes neither historical priority nor the absence of unpublished parallel work. No first-discovery claim is made here.

## Computational certificates and evidence boundaries

The proof has five finite computations: C1, C2, C1g, C2g and the final anchor box. Their exact domains and target inequalities appear in technical subdivision 10. The analytic argument reduces arbitrary nonnegative integer profiles to these domains. Each reduction must be checked separately from the program output.

For the profile box the recorded primary implementation floors every rational summand after multiplication by $2^{40}$. Min-plus products produce a lower bound; every candidate not excluded by that lower bound is evaluated as an exact rational number. Feasibility is encoded by excluded matrix entries. The tail implementation computes the auxiliary minimum $\kappa^*$ exactly over $23\leq p\leq160$ and checks positivity and monotonicity of its numerator beyond that range. Correct integer ranges, sentinel separation and the exhaustiveness of candidate enumeration are part of the certificate specification.

| Certificate | Recorded result | Verification obligation |
| --- | --- | --- |
| C1 | $\Phi_{\rm prof}\geq23/12$ on the feasible box, $t\leq11$ | Exact primary, directed-rounding cross-check, and additional integer-only check for $t\leq1$. |
| C2 | Tail contribution at least $11/12$; two equality gadgets | Exact tail cutoff and separation of minimisations. |
| C1g | Threshold $2$; 41 ties for $t\geq2$ | All four noncompliant classes and all three positions for $t=1$. |
| C2g | Tail threshold $1$; eight ties for $t\geq2$ | Correct masks for the one-type-2-slot cases. |
| Final box | 3,279 admissible points; unique equality $(1,0,1,0)$ | Exclude the impossible mutual configuration; verify all admissibility implications. |

The historical evidence includes an exact primary implementation and an independent cross-check for each finite claim. For C1 with $t\leq1$, the historical cross-check uses rigorous directed floating-point rounding. A newer integer-only implementation checks the four type-count cases on $\{0,\ldots,92\}^6$ using rational matrix construction and scale $2^{32}$. Its smallest certified lower bound is $8277463527/4294967296$, exceeding $23/12$ by $136328629/12884901888$. It bounds every profile but does not certify the exact minimum or all minimisers. It was written after inspecting the primary checker and shares its method; it is a separate implementation, not a blind independent proof review. The existing exact C1g check covers $t\geq2$.

Six checks passed a clean replay of a copied package in a fresh virtual environment, using CPython 3.14.7 and NumPy 2.5.4 with a hash-pinned offline macOS arm64 wheel. This was a same-machine replay: the operating system and interpreter were not rebuilt, and neither cross-platform nor human reproduction is claimed. The recorded corrected final box contains 3,279 points; the obsolete larger count included 122 impossible mutual configurations.

The separate reproducibility record contains sources, commands, versions, hashes and replay outputs. A source-level AI check matched the finite profile equations, domains, admissibility masks and integer pruning to the supplementary programs. This check does not establish the universal host-to-profile reductions or replace their written proofs. Finite-host stress tests corroborate written arguments but are not substitutes for proof certificates.

## Formal verification ledger

| Claim | Evidence in this draft |
| --- | --- |
| Main theorem | The exact shadow–co-link inequality and coefficient-one bound in `Erdos643R3.CoefficientOneFinal` have complete official Lean verification and independent exact-source acceptance in the isolated proof project. The exact transformed supplementary source package has separately passed its complete check. |
| Local $23/12$ bound | `Erdos643R3.Pw2312Main.per_triple`: $23/12\leq\sigma_W(H,T)+\tau_W(H,T)$ for each $T\in H$ under uniformity and forbidden-configuration avoidance. Historical official passing receipt recorded. |
| Global $24/23$ bound | `Erdos643R3.Pw2312Main.card_le_choose`: $\vert H\vert \leq(24/23)\binom{\vert V\vert }{2}$. Historical official passing receipt recorded. |
| Intermediate bounds | `Erdos643R3.Pw2312Main.card_le_shadow_colink`, `Erdos643R3.Pw2312Main.card_le_O`, and profile bound `Erdos643R3.Pw2312Main.theorem2` belong to the same source-matched verified module. |
| Charge identity | `Erdos643R3.L1Top.sum_charge` and `Erdos643R3.L1Top.sum_charge_eq_neg_Phi` are in the exported module covered by the build, scan and kernel replay described below. |
| Conservation and split | `Erdos643R3.L1Top.sum_final_eq_neg_Phi` and `Erdos643R3.L1Top.rule2p_split` have the same exported-module coverage. |
| Nonnegative charges | `Erdos643R3.L1Top.final_nonneg_of_charge_nonneg` and `Erdos643R3.L1Top.final_eq_zero_of_donor` have that module coverage. These do not establish recovery of deficient triples. |
| Conditional endpoint | `Erdos643R3.L1Top.conditional_endpoint` assumes that every deficient triple is recovered. A proof of this conditional statement leaves the main obligation unpaid. |
| Local structure and anchor estimates | The new unconditional source imports the structural and anchor chain, covered by the accepted complete 65-module core verification. This does not certify every written formulation in this exposition. |
| Finite certificates | Supporting C1/C2 certificates enter the verified $23/12$ module. This does not formally verify all strengthened certificates or the full coefficient-1 argument. |

The receipt check matched all 13 source-module hashes and inspected six relevant official passing logs. The local and global declarations above have zero `sorry` or `native_decide` occurrences and only the allowed axioms `propext`, `Classical.choice` and `Quot.sound`. These are reused source-matched receipts, not new Lean runs for this manuscript. The supplementary formal-evidence ledger records the historical receipt hashes and the separately tracked export transformations; original source hashes must not be identified with transformed export hashes. Current export-check outcomes are recorded separately in the supplementary verification document and formal-evidence ledger. The historical receipts here apply only to their original source and import-closure hashes. Their scope is the $23/12$ local and $24/23$ global bounds; they do not certify the stronger coefficient-1 theorem. The new unconditional source has its own accepted complete passing receipt, described below.

**Verification and review.** The unconditional final source has an accepted official passing receipt, complete dependency replay, allowed-axiom audit and independent exact-source acceptance. The expanded transformed supplementary source package passed its complete 126-module check, including general design existence and the exact admissible-order values. Historical module-level coverage is described separately. No proof using `sorry` or `native_decide` would satisfy that requirement. Compilation of a helper, documentation validation, or a passing conditional endpoint is not formal verification of the [main theorem](#the-problem-and-result).

The supplementary phased verification receipt includes the comment-sanitized `L1Top` module in 20 fresh module builds, source scans and independent kernel replay in three disjoint chunks. Its 50 individual supporting-declaration checks do not include the L1Top statements listed here. The module source and replay hashes are recorded in [historical phased receipt](formal-evidence/receipts-export/hardened-phased/receipt.json). A separate monolithic replay reached its 240-second limit and remains unknown; it is not counted as a successful replay. The conditional endpoint still assumes that every deficient triple receives enough charge. Neither the supporting-module replay nor the conditional theorem proves that assumption.

**Unconditional final source and exact corollaries.**
The new final source contains nine unconditional declarations and one declaration conditional on a supplied block design. They are listed below by their exact names in the namespace `Erdos643R3.CoefficientOneFinal`. The exact ten exports have accepted complete official verification in the isolated proof project; the inventory identifies that scope and does not itself replace the receipt.

| Declaration suffix | Exact scope |
| --- | --- |
| `coefficient_one` | Finite coefficient-one bound for every finite avoiding triple system. |
| `phi_nonpos` | Nonpositivity of the manuscript potential under uniformity and avoidance. |
| `shadow_colink_bound` | The exact shadow–co-link inequality of the [main theorem](#the-problem-and-result). |
| `extremal_three_le_choose_two` | Upper bound for the imported extremal number at every natural order. |
| `forcing_three_le_choose_two_add_one` | Corresponding extremal-number-plus-one forcing bound. |
| `extremal_three_bounds` | Finite star lower bound and coefficient-one upper bound together. |
| `extremal_three_lower_matching` | Star-plus-matching lower bound at each positive natural order. |
| `extremal_ratio_tendsto_one` | Ratio of the imported extremal number to the pair count tends to one. |
| `forcing_isEquivalent` | The imported forcing threshold is asymptotically equivalent to the pair count. |
| `extremal_eq_of_supplied_design` | Exact equality assuming an actual supplied two-design with block size five and pair multiplicity one. |

The supplied-design declaration retains its displayed design hypothesis. The expanded proof package separately discharges that hypothesis at every admissible order: it constructs an actual two-design on the given finite vertex type, with block size five and every vertex pair in exactly one block. The construction is unconditional apart from the stated residue condition, including order one. The resulting extremal equality and forcing-plus-one equality are verified consequences. This formalizes the classical existence result of Hanani. The original 1961 paper and 1965 completion were visually read; that reading is not an independent validation of every finite table or block entry, or a formal audit of the historical proofs. The star construction suffices for the unconditional asymptotic consequence; no general design-existence theorem is an input to that consequence.

**Verification and review.** The official core checker printed `RESULT: PASS`; the accepted receipt covers the ten exact final exports, 65 fresh module builds and source scans, complete independent kernel replay in 33 bounded chunks, twelve named declaration and axiom checks, and matching binary pins before and after the run. Only `propext`, `Classical.choice` and `Quot.sound` occur as axioms; no `sorry` or `native_decide` is permitted. The earlier portable supplementary checker passed on its 69 exact exported modules, including the explicit one- and five-vertex design consequences. The expanded combined package separately passed its complete official check on all 126 exact modules, including general design existence: 126 fresh builds, full independent kernel replay in bounded chunks, twenty-three exact declaration/module/axiom checks, whole-closure source and hygiene scans, and binary pins before and after the check. Dependency setup cloned the pinned revisions into a fresh directory and obtained the official cache on the same machine; this is not independent reproduction on another machine. Formal coverage does not automatically extend to every intermediate exposition, example, or historical computation.

**Classical design construction and exact values.**
The expanded package includes three additional exact endpoints. Their shared order condition is that the natural order has residue one or five modulo twenty. The existence declaration constructs an actual finite upstream block design. At order one, the block family is empty and the pair-coverage condition is vacuous; the original triple extremal value is directly zero. Order five uses the single five-point block. These boundary cases are separate from the classical nontrivial five-block designs attributed to Hanani. Concrete finite seeds and transversal inputs are supplied by proved constructions; no free seed or recursive-existence premise remains at these endpoints.

`Erdos643Design.HananiExistence.exists_design` constructs the actual two-design with block size five and pair multiplicity one. `Erdos643R3.CoefficientOneHanani.extremal_eq` proves that the original disjoint-union-free triple extremal number equals the pair count at every admissible order. `Erdos643R3.CoefficientOneFullSolution.forcing_eq` proves that the forcing threshold, namely the extremal number plus one, equals the pair count plus one at every admissible order. These statements formalize a classical construction and its exact-value consequence. They do not classify every extremal host, prove a higher-uniformity result or establish priority. Formal verification and AI source review do not constitute human mathematical review.

**Authorship and review provenance.**
Robert Huynh directed the research and preparation of this draft. AI systems developed proof arguments, implemented finite computations, assisted formalization, checked parts of the mathematics and prepared the exposition. These activities do not constitute human mathematical endorsement or establish independence, correctness or priority. No human verification of any mathematical step is claimed.

**Formal target.**
The target recorded in `FormalConjectures/ErdosProblems/643.lean` is `Erdos643.erdos_643.parts.ii`, the asymptotic forcing statement for all $t\ge3$. Its $t=3$ specialization requires

$$
\bigl(\operatorname{extremalNumber}(n,3,\neg\operatorname{HasRepeatedDisjointUnion})+1\bigr)
 \sim\binom n2.
$$

The verified $24/23$ bound does not prove this specialization. The new final source includes the host-to-extremal bridge, unconditional coefficient-one upper bound, star lower bound and asymptotic consequence. Its complete official check and independent exact-source acceptance are recorded for the isolated proof project. The exact expanded supplementary source package also passed its complete check: all 126 modules were rebuilt and independently kernel-replayed, with twenty-three named declaration and axiom checks. Its general design-existence theorem and exact admissible-order values are separate from the asymptotic squeeze, which uses only the star lower bound. The supplied Lean proof covers the triple case; the combined conclusion for every fixed uniformity at least three additionally relies on Huang, Ma and Yang's external preprint.

## Detailed written argument

The numbered subdivisions 2–10 in this appendix form a single technical sequence. References to these numbers within the appendix refer to that sequence. The definitions preceding it are collected in Section [Conventions and the counting identity](#conventions-and-the-counting-identity). Lemmas S1–S11, Proposition S2 and Theorems S1 and S1' belong to subdivision 7; Theorem S3 belongs to subdivision 8. Unprefixed numerical slot lemmas belong to subdivision 2, and the suffix g identifies the strengthened profile argument. This presentation preserves the full critical proof path, including its finite certificate obligations.

### 2. The slot model and the $23/12$ bound

#### 2.1 Two facts about common links

**F1.**  If $H$ is avoiding, every $\operatorname{CN}(x,y)$ is intersecting.

*Proof.*
If $P,Q\in\operatorname{CN}(x,y)$ were disjoint, the four triples

$$
P\cup\{x\},\quad Q\cup\{y\},\quad Q\cup\{x\},\quad P\cup\{y\}
$$

would be distinct edges of $H$. The first two are disjoint, the last two are disjoint, and both unions are $P\cup Q\cup\{x,y\}$. This is the forbidden configuration.
 ∎

**F2.**  For every $3$-graph $H$, without an avoidance hypothesis,

$$
\sum_{T\in H}\sigma(T)=|\partial H|,
 \qquad \sum_{T\in H}\tau(T)=|\operatorname{CL}(H)|.
$$

*Proof.*
A pair $p\in\partial H$ lies in exactly $k_p$ triples and contributes $1/k_p$ to each. For $q=xy\in\operatorname{CL}(H)$, write $\operatorname{CN}(q)=\{P_1,\ldots,P_s\}$. The option $q$ occurs in each of the $2s$ distinct triples $P_i\cup\{x\}$ and $P_i\cup\{y\}$. Conversely, if $q$ is an option of $T$ through $P$, then $P\in\operatorname{CN}(q)$ and $T=P\cup(q\cap T)$. Since $q$ meets $T$ only in its opposite vertex, it cannot occur through two different pairs of $T$. Thus $q$ contributes $2s/(2s)=1$, and every option belongs to $\operatorname{CL}(H)$.
 ∎

Consequently, with $\Phi(H)=2\vert H\vert -\vert \partial H\vert -\vert \operatorname{CL}(H)\vert$,

$$
\sum_{T\in H}c(T)=-\Phi(H).
$$

#### 2.2 The slot lemmas

**Lemma 1.**  For every slot $v$ of $T$, its option $q_v$ satisfies $s_{q_v}=1+d(v)$.

*Proof.*
Take $T=abc$ and $v=(z,A)$; the other groups follow by renaming. Then $q_v=az$ and $bc\in\operatorname{CN}(a,z)$. By F1 every member of $\operatorname{CN}(a,z)$ meets $bc$. Members through $b$, other than $bc$, are precisely $bu$ with $(u,C)$ adjacent to $(z,A)$ in $R_b$: indeed $abu,buz\in H$ is equivalent to $u\in C$, $u\ne z$ and the relation edge. Members through $c$, other than $bc$, similarly correspond to neighbours in $R_c$. Only $bc$ contains both $b$ and $c$. Therefore

$$
s_{az}=1+d_{R_b}(v)+d_{R_c}(v).
$$

Avoidance is used here only to ensure that every common-link member meets $bc$.
 ∎

**Lemma 2.**  A slot with neighbours in both relations has exactly one neighbour in each, and those two slots represent the same vertex.

*Proof.*
Again take $v=(z,A)$. If $(u,C)$ is an $R_b$-neighbour and $(u',B)$ is an $R_c$-neighbour, then $bu,cu'\in\operatorname{CN}(a,z)$. These pairs intersect by F1. Since $b\ne c$, $b\notin\{c,u'\}$ and $c\notin\{b,u\}$, necessarily $u=u'$. Every neighbour in either relation is therefore a slot of one fixed vertex, and a vertex has at most one slot in each group.
 ∎

Thus a type-2 slot has degree two, cost $1/6$, and common link $\{bc,bw,cw\}$, a triangle. A type-1 slot has a star common link, and an isolated slot has common-link size one and cost $1/2$. In particular,

$$
\tau(T)=\sum_{v\text{ a slot of }T}\frac1{2(1+d(v))}.
$$

The exact equivalence between type-2 slots and triangle options is also proved in Lemma 1g(a), subdivision 4.1.

#### 2.3 The profile function

The six type-1 counts are denoted $ab,ac,bc,ba,ca,cb$: the first letter identifies the group and the second the apex of the relation. In expressions such as $ab$ in this subdivision, the symbol denotes a count, not the product of two variables or a vertex pair. Let $t_A,t_B,t_C$ count type-2 slots and put

$$
n_A=ab+ac+t_A,\quad n_B=bc+ba+t_B,\quad
 n_C=ca+cb+t_C,\quad t=t_A+t_B+t_C.
$$

For nonnegative integers $p,q,y$, define

$$
S(p,q,y)=\begin{cases}\displaystyle\frac{p^2}{2(p+pq+y)},&p\geq1,\\[3pt]0,&p=0.\end{cases}
$$

Define

$$
\begin{aligned}
 \Phi_{\rm prof}={}&\frac1{1+n_A}+\frac1{1+n_B}+\frac1{1+n_C}+\frac t6+e_c+e_a+e_b,\\
 e_c={}&S(ac,bc,t_B)+S(bc,ac,t_A),\\
 e_a={}&S(ba,ca,t_C)+S(ca,ba,t_B),\\
 e_b={}&S(cb,ab,t_A)+S(ab,cb,t_C).
\end{aligned}
$$

Feasibility (F) means

$$
\begin{aligned}
 ac+t_A\geq1&\iff bc+t_B\geq1,\\
 ba+t_B\geq1&\iff ca+t_C\geq1,\\
 cb+t_C\geq1&\iff ab+t_A\geq1.
\end{aligned}
$$

For the cyclic notation, let $(X_0,X_1,X_2)=(A,B,C)$ and $(\rho_0,\rho_1,\rho_2)=(R_c,R_a,R_b)$. The counts in $X_i$ for $\rho_i,\rho_{i-1}$ are $f_i,g_i$, respectively; all indices are modulo three. Thus

$$
(f_0,g_0)=(ac,ab),\quad(f_1,g_1)=(ba,bc),\quad(f_2,g_2)=(cb,ca),\quad n_i=f_i+g_i+t_i.
$$

Then

$$
\Phi_{\rm prof}=\sum_{i=0}^2\left[
 \frac1{1+f_i+g_i+t_i}+\frac{t_i}{6}
 +S(f_i,g_{i+1},t_{i+1})+S(g_{i+1},f_i,t_i)\right],
$$

and (F) is $f_i+t_i\geq1\iff g_{i+1}+t_{i+1}\geq1$ for each $i$. Both are invariant under cyclic shift.

**Lemma $3^+$.**  Let $i_X$ count isolated slots of group $X$. The profile satisfies (F), and

$$
\sigma(T)+\tau(T)\geq\Phi_{\rm prof}^+
 :=\Phi_{\rm prof}+\sum_X\Delta_X,\qquad
 \Delta_X=\frac1{1+n_X+i_X}+\frac{i_X}2-\frac1{1+n_X}\geq0.
$$

*Proof.*
For a relation $\rho$ joining groups $X,Y$, let $P,Q$ be their respective sets of type-1 slots in $\rho$, and let $S_Y$ be the type-2 slots of $Y$. Every neighbour of a slot in $P$ lies in $Q\cup S_Y$; each member of $S_Y$ has exactly one $\rho$-neighbour. Hence

$$
\sum_{v\in P}d(v)\leq |P||Q|+|S_Y|,
 \qquad
 \sum_{v\in P}\frac1{2(1+d(v))}
 \geq\frac{|P|^2}{2\sum_{v\in P}(1+d(v))}
 \geq S(|P|,|Q|,|S_Y|),
$$

where the zero-size case is interpreted directly as zero. Summing the six choices of side and relation, and adding the type-2 and isolated costs, gives the stated inequality, since $k=1+n_X+i_X$ for the corresponding pair. The increment from inserting one isolated slot is nonnegative because $1/(1+m)+1/2\geq1/m$ for $m\geq1$. Finally, positive degree on either side of a relation requires positive degree on the other, proving (F).
 ∎

**Lemma 3.**  Every triple has a feasible profile and $\sigma(T)+\tau(T)\geq\Phi_{\rm prof}$. This follows from Lemma $3^+$.

#### 2.4 The profile lower bound

**Theorem 2.**  Every feasible nonnegative integer profile satisfies $\Phi_{\rm prof}\geq23/12$.

We first record four elementary inequalities, with nonnegative integer arguments unless otherwise indicated.

- **(E1)**  For $p\geq1$,

$$
S(p,q,y)\geq\frac{p}{2(1+q)}-\frac{y}{2(1+q)^2}.
$$

  Indeed $2S=p/(1+q+y/p)$ and $1/(a+e)\geq1/a-e/a^2$ for $a>0,e\geq0$.

- **(E2)**  $S(p,q,y)$ is nondecreasing in $p$ and nonincreasing in $q,y$. For positive $p$, the numerator determining its $p$-derivative is $p^2(1+q)+2py\geq0$; the extension at zero is consistent.

- **(E3)**  For real $p,q\geq0$, put $r=(1+p)/(1+q)$. Then

$$
\frac12\left(\frac p{1+q}+\frac q{1+p}\right)
 =\frac12\left(r+\frac1r\right)-\frac12\left(\frac1{1+p}+\frac1{1+q}\right)
 \geq1-\frac12\left(\frac1{1+p}+\frac1{1+q}\right).
$$

- **(E4)**  For a relation with type-1 counts $p,q\geq1$ and type-2 counts $x,y$ on the respective sides,

$$
S(p,q,y)+S(q,p,x)\geq1-\frac12\left(\frac1{1+p}+\frac1{1+q}\right)
 -\frac{y}{2(1+q)^2}-\frac{x}{2(1+p)^2}.
$$

  This follows from (E1) and (E3).

*Proof of Theorem 2.*
Nonnegativity of the terms gives $\Phi_{\rm prof}\geq t/6$, so assume $t\leq11$. A relation is *big* if both its type-1 counts are at least 23. If a non-big relation has one count $p\geq93$, its other count is $q\leq22$, and (E2) gives

$$
\Phi_{\rm prof}\geq S(93,22,11)=\frac{8649}{4300}>\frac{23}{12},
$$

since $8649\cdot12=103788>98900=23\cdot4300$. Thus all counts in non-big relations may be bounded by 92. The smaller cutoff 92 would suffice only for the threshold $23/12$: $S(92,22,11)=4232/2127<2$, so the threshold-$2$ reduction in subdivision 4.3 retains cutoff 93.

If at least two relations are big, each contributes at least $1-1/24-(x+y)/1152$ by (E4). Two relations share one group, so their four type-2 counts sum to at most $2t$. Consequently

$$
\Phi_{\rm prof}\geq\frac t6+2-\frac1{12}-\frac{2t}{1152}\geq\frac{23}{12}.
$$

If no relation is big, all six type-1 counts are in $\{0,\ldots,92\}$ and $t\leq11$. This is precisely finite certificate C1, stated in subdivision 10.

It remains to consider exactly one big relation, which by cyclic symmetry is $R_c$. Thus $ac,bc\geq23$ and $ab,ba,ca,cb\leq92$. Write

$$
K=\frac1{1+n_A}+\frac1{1+n_B}+e_c,\qquad
 G=\frac1{1+n_C}+\frac t6+e_a+e_b.
$$

Put $u=ab+t_A$, $v=ba+t_B$ and

$$
\kappa(p;u,s)=\frac1{1+p+u}-\frac1{2(1+p)}-\frac{s}{2(1+p)^2},\qquad
 \kappa^*(u,s)=\min\left(0,\inf_{p\in\mathbb Z,\,p\geq23}\kappa(p;u,s)\right).
$$

By (E4), with the $t_A$ discount belonging to the term $S(bc,ac,t_A)$,

$$
K\geq1+\kappa(ac;u,t_A)+\kappa(bc;v,t_B),
$$

and hence

$$
\Phi_{\rm prof}\geq1+G+\kappa^*(ab+t_A,t_A)+\kappa^*(ba+t_B,t_B).
$$

Certificate C2 proves that the last three terms sum to at least $11/12$ for every remaining profile satisfying (F) for $R_a,R_b$. The third relation is automatically feasible. These cases exhaust all profiles.
 ∎

For completeness, with $x=1+p$,

$$
\kappa(p;u,s)=\frac{x^2-(u+s)x-su}{2x^2(x+u)}.
$$

The numerator is positive for

$$
x>x_+:=\frac{u+s+\sqrt{(u+s)^2+4su}}2.
$$

In C2, $u\leq103,s\leq11$, so $x_+<160$. Every negative infimum is therefore attained in $23\leq p\leq160$; otherwise the minimum with zero is zero. This analytic cutoff is part of the certificate justification.

#### 2.5 The per-triple bound

**Theorem 1.**  Every triple of a finite avoiding $3$-graph satisfies $\sigma(T)+\tau(T)\geq23/12$. In particular every deficient triple has $\operatorname{def}(T)\leq1/12$.

*Proof.*  Apply Lemma 3 and Theorem 2. ∎

An intermediate consequence, not used later, is

$$
\frac{23}{12}|H|\leq|\partial H|+|\operatorname{CL}(H)|,
$$

and, writing $O(H)=\partial H\cup\operatorname{CL}(H)$,

$$
|H|\leq\frac{12}{23}(|\partial H|+|\operatorname{CL}(H)|)
 \leq\frac{24}{23}\max\{|\partial H|,|\operatorname{CL}(H)|\}
 \leq\frac{24}{23}|O(H)|\leq\frac{24}{23}\binom n2.
$$

This follows by summing Theorem 1 and using F2.

### 3. Triples without a triangle option

#### 3.1 Theorem A

**Theorem A.**  If $H$ is avoiding and $T\in H$ has no option with triangular common link, then $\sigma(T)+\tau(T)>2$.

**Lemma 3g.**  Every feasible profile with $t=0$ satisfies $\Phi_{\rm prof}>2$.

*Proof.*
With $t=0$, $S(p,q,0)=p/(2(1+q))$, including $p=0$. Put

$$
g(p,q)=\frac12\left(\frac p{1+q}+\frac q{1+p}\right).
$$

Then

$$
\Phi_{\rm prof}=\sum_{i=0}^2\frac1{1+n_i}
       +\sum_{i=0}^2g(f_i,g_{i+1}),\qquad n_i=f_i+g_i,
$$

and (F) reads $f_i\geq1\iff g_{i+1}\geq1$. We use three inequalities.

- **(G1)**  For integers $p,q\geq0$, $g(p,q)+1/(1+p)\geq1$. Multiplication by $2(1+p)(1+q)$ reduces this to $(p-q)(p-q-1)\geq0$.

- **(G2)**  $g(p,q)\geq1-\tfrac12(1/(1+p)+1/(1+q))$, by (E3).

- **(G3)**  For integers $x,y\geq1$,

$$
\frac12\left(\frac1{1+x}+\frac1{1+y}\right)-\frac1{1+x+y}\leq\frac14.
$$

  Indeed, put $u=1/(1+x)$ and $v=1/(1+y)$, both in $(0,1/2]$. Since $1+x+y\leq(u+v)/(uv)$, the left side is at most

$$
\frac{u+v}{2}-\frac{uv}{u+v}
 =\frac{u^2+v^2}{2(u+v)}\leq\frac{\max(u,v)}2\leq\frac14.
$$

Let $r$ be the number of nonempty relations, equivalently the number of indices with $f_i\geq1$. We may cyclically rotate their indices.

If $r=0$, all counts vanish and $\Phi_{\rm prof}=3$.

If $r=1$, take $\rho_0$ nonempty. Then $n_0=f_0,n_1=g_1,n_2=0$, and (G1) gives

$$
\Phi_{\rm prof}=\frac1{1+f_0}+\frac1{1+g_1}+1+g(f_0,g_1)
 \geq2+\frac1{1+g_1}>2.
$$

If $r=2$, take $\rho_0$ empty, so $f_0=g_1=0$, $n_0=g_0$ and $n_1=f_1$. By (G1) twice and symmetry of $g$,

$$
\Phi_{\rm prof}=\left[\frac1{1+f_1}+g(f_1,g_2)\right]
 +\left[\frac1{1+g_0}+g(g_0,f_2)\right]+\frac1{1+n_2}
 \geq2+\frac1{1+n_2}>2.
$$

If $r=3$, all six type-1 counts are positive. Apply (G2) to every relation and (G3) to every group:

$$
\Phi_{\rm prof}\geq3-\sum_{i=0}^2\left[
 \frac12\left(\frac1{1+f_i}+\frac1{1+g_i}\right)-\frac1{1+f_i+g_i}\right]
 \geq3-\frac34>2.
$$

These four cases prove the lemma.
 ∎

A type-2 slot has a triangular common link, so the hypothesis of Theorem A forces $t=0$. Lemma 3 gives $\sigma(T)+\tau(T)\geq\Phi_{\rm prof}$, proving Theorem A.

### 4. Structure of deficient triples

**Theorem G1.**  Let $T\in H$ be deficient in an avoiding $3$-graph. Then:

- **(i)**  $T$ has exactly one triangle option $q=xy$, with $x\in T$. Write $\operatorname{CN}(q)=\{uv,vw,uw\}$ and $T=x+uv$.

- **(ii)**  Exactly one of $xu,xv$ is light.

- **(iii)**  If $xu$ is light, then $L(xu)=\{v,w\}$ and $s_{vw}=2$. If $xv$ is light, then $L(xv)=\{u,w\}$ and $s_{uw}=2$.

Moreover $T$ has no isolated slot, and its precise slot structure is given by Corollary 6g below. The inputs are F1, the slot and profile lemmas of subdivision 2, the profile theorem there, and Lemma 3g. No redistribution conclusion is used.

#### 4.1 Translation into profiles

**Lemma 1g.**  Fix $T=abc$ in an avoiding $H$.

- **(a)**  Triangle options are exactly the options of type-2 slots. Distinct slots give distinct options. Thus $T$ has $t$ triangle options.

- **(b)**  If $(z,A)$ is type 2, with partner slots $(w,B),(w,C)$, then $\operatorname{CN}(a,z)=\{bc,bw,cw\}$. The pair $ab$ is light exactly when $\vert C\vert =1$, in which case $C=\{w\}$ and $L(ab)=\{c,w\}$. The corresponding assertion for $ac,B$ also holds.

- **(c)**  If $t=1$, then $(w,B)$ is type 1 in $R_c$ and $(w,C)$ is type 1 in $R_b$. Hence $bc,cb\geq1$, where these symbols denote profile counts.

- **(d)**  If $t=1$ and $C=\{w\}$, then $s_{cw}=2+ab$ and the option through the pair $ab$ is $cw$. Symmetrically, if $B=\{w\}$, then $s_{bw}=2+ac$.

All assertions rotate cyclically with $a,b,c$.

*Proof.*
For (a), the members of $\operatorname{CN}(a,z)$ are $bc$, the pairs $bu$ coming from $R_b$-neighbours, and the pairs $cu$ coming from $R_c$-neighbours. Lemma 2 gives the triangle $\{bc,bw,cw\}$ for a type-2 slot. An isolated slot gives just one pair. A type-1 slot gives pairs with a common vertex, hence cannot give a triangle. Options of distinct slots are distinct because an option meets $T$ only at its opposite vertex.
For (b), $k_{ab}=1+\vert C\vert$ and $w\in C$; similarly for $ac$. For (c), each partner slot has its edge to $(z,A)$, and cannot be type 2 because that would give a second type-2 slot.
For (d), the slot $(w,C)$ has as $R_b$-neighbours the type-2 slot $(z,A)$ and every slot counted by $ab$: a type-1 slot in $R_b$ needs a neighbour, and $C$ consists only of $w$. It has no $R_a$-neighbour, since it is not type 2. Its degree is $1+ab$, giving $s_{cw}=2+ab$ by Lemma 1. The mirror assertion is identical after exchanging $B,C$.
 ∎

A feasible profile with $t=1$ and its type-2 slot in $X_i$ is *G1-compliant* when exactly one of $n_{i+1}=1,n_{i-1}=1$ holds and

$$
n_{i-1}=1\Longrightarrow g_i=0,\qquad n_{i+1}=1\Longrightarrow f_i=0.
$$

Its *partner constraints* are $g_{i+1}\geq1$ and $f_{i-1}\geq1$. These follow already from (F) when $t=1$. All these notions are invariant under cyclic shift.

**Corollary 1g.**  If $T$ has exactly one type-2 slot and no isolated slot, its profile satisfies the partner constraints, and conclusions (i)–(iii) of G1 are equivalent to G1-compliance.

*Proof.*
Rotate to $i=0$. Lemma 1g(c) gives the partner constraints. Without isolated slots, $\vert B\vert =n_B$ and $\vert C\vert =n_C$. By Lemma 1g(b), exactly one light pair means exactly one of $n_B,n_C$ equals one. By Lemma 1g(d), the required common-link size two then says $ab=g_0=0$ if $C=\{w\}$, or $ac=f_0=0$ if $B=\{w\}$. The link identity in G1(iii) is part of Lemma 1g(b).
 ∎

#### 4.2 Isolated slots

**Lemma 2g.**  A triple with exactly one type-2 slot and at least one isolated slot satisfies $\sigma(T)+\tau(T)\geq9/4$.

*Proof.*
Rotate its type-2 slot to $(z,A)$. Each group has at least one non-isolated slot, by Lemma 1g(c). For $n\geq1$, define

$$
D(i)=\frac1{1+n+i}+\frac i2-\frac1{1+n},\qquad i\geq0.
$$

Then $D(0)=0$ and

$$
D(i+1)-D(i)=\frac12-\frac1{(1+n+i)(2+n+i)}\geq\frac13.
$$

One isolated slot therefore supplies a correction at least $1/3$ in Lemma $3^+$. Theorem 2 gives $\sigma+\tau\geq23/12+1/3=9/4$.
 ∎

#### 4.3 The threshold-two profile theorem

**Theorem 4g.**  For every feasible profile: (a) $t\geq2$ implies $\Phi_{\rm prof}\geq2$; (b) if $t=1$, the partner constraints hold, and the profile is not G1-compliant, then $\Phi_{\rm prof}\geq2$.
Equality in (a) occurs at the complete five-vertex profile $t_A=t_B=t_C=2$, with all type-1 counts zero. Only the bound two is asserted in (b).

*Proof.*
The bound $\Phi_{\rm prof}\geq t/6$ disposes of $t\geq12$, so take $1\leq t\leq11$. A big relation again has both type-1 counts at least 23.
For at least two big relations, the estimate in Theorem 2 gives

$$
\Phi_{\rm prof}\geq2+t\left(\frac16-\frac1{576}\right)-\frac1{12}
 \geq2+\frac{95}{576}-\frac{48}{576}>2.
$$

For a non-big relation with one count at least 93, (E2) gives $\Phi_{\rm prof}\geq8649/4300>2$. Thus every count of a non-big relation can be restricted to $0,\ldots,92$.
If no relation is big, certificate C1g proves (a) for the 360 triples of type-2 counts satisfying $2\leq t\leq11$. Exactly 41 feasible profiles attain two. For $t=1$, let $i$ be the position of the type-2 slot. Under the partner constraints, the noncompliant profiles are precisely the union of

$$
\begin{aligned}
 V1:&\quad n_{i+1}\geq2,\quad n_{i-1}\geq2;\\
 V2:&\quad n_{i+1}=n_{i-1}=1;\\
 V3:&\quad n_{i-1}=1,\quad g_i\geq1;\\
 V4:&\quad n_{i+1}=1,\quad f_i\geq1.
\end{aligned}
$$

Indeed both neighbouring group sizes are at least one, so these are exactly the negation of G1-compliance. Each class is expressible as masks on the three group matrices of the profile cycle. The C1g computation minimises over those masks, for all three positions, and gives the bound two in every class.
If exactly one relation is big, rotate it to $R_c$. The notation of Theorem 2 gives

$$
\Phi_{\rm prof}\geq1+W,\qquad
 W=G+\kappa^*(ab+t_A,t_A)+\kappa^*(ba+t_B,t_B),
$$

where $ab,ba,ca,cb\in\{0,\ldots,92\}$ and $n_A,n_B\geq23$. For $t=1$ the compliance alternatives are:

-  $(t_A,t_B,t_C)=(1,0,0)$: compliance means $n_C=ca+cb=1$ and $ab=0$; the partner constraint is $cb\geq1$.

-  $(t_A,t_B,t_C)=(0,1,0)$: compliance means $n_C=1$ and $ba=0$; the partner constraint is $ca\geq1$.

-  $(t_A,t_B,t_C)=(0,0,1)$: compliance is impossible since both neighbouring groups have more than one slot.

Certificate C2g gives $W\geq1$ for $2\leq t\leq11$ and for every noncompliant $t=1$ rest profile, with or without the partner constraints. There are eight target-equality profiles in the former range. Hence $\Phi_{\rm prof}\geq2$. The cases are exhaustive, including the earlier reduction of every large one-sided count.
 ∎

#### 4.4 G1 and the precise slot structure

*Proof of Theorem G1.*
For deficient $T$, Lemma $3^+$ gives

$$
\Phi_{\rm prof}\leq\Phi_{\rm prof}^+\leq\sigma(T)+\tau(T)<2.
$$

Lemma 3g forces $t\geq1$ and Theorem 4g(a) forces $t\leq1$. Thus $t=1$. Lemma 2g excludes isolated slots. Corollary 1g supplies the partner constraints, Theorem 4g(b) forces compliance, and Corollary 1g translates compliance into G1(i)–(iii).
 ∎

The strict hypothesis is necessary: every triple of the complete five-vertex $3$-graph has $\sigma+\tau=2$ and six triangle options. Exactly one triangle option is equivalent to membership in exactly one bicone.

**Corollary 6g.**  Suppose $T=abc$ is deficient, its type-2 slot is $(z,A)$ with partner $w$, and $C=\{w\}$, so the pair $ab$ is light. Then

$$
t_A=1,\quad t_B=t_C=0,\quad ab=ca=ba=0,\quad cb=1,
$$

with no isolated slots. Every slot of $A$ except $(z,A)$ and every slot of $B$ is type 1 in $R_c$. The relation $R_b$ consists of the single edge $(w,C)(z,A)$, and $R_a$ is empty. In particular $\vert B\vert =bc$ and $\vert A\vert =1+ac$.

*Proof.*
G1(iii) and Lemma 1g(d) give $ab=0$. The only slot of $C$ is type 1 in $R_b$, so $cb=1,ca=t_C=0$. As $t=1$, also $t_B=0$. Feasibility for $R_a$ forces $ba=0$. The remaining assertions follow directly from these counts and absence of isolated slots.
 ∎

### 5. Redistribution and both-light anchors

Every deficient triple lies in an active bicone by G1 (already by Theorem A), not merely by definition of the redistribution rule. This coverage is a separate mathematical input.

**Lemma D.**  Under Rule $2'$, each triple of nonnegative initial charge has nonnegative final charge, every donor ends at zero, and the total charge is unchanged.

*Proof.*
A donor $T'$ sends $c(T')/\operatorname{act}(T')$ to each of its $\operatorname{act}(T')$ active bicones, hence sends exactly $c(T')$. It receives nothing because only deficient triples receive. Other nonnegative triples are untouched. For each active bicone, $D_q$ is nonempty and all its deficits are positive, so

$$
\sum_{T\in D_q}\frac{\operatorname{def}(T)}{\sum_{S\in D_q}\operatorname{def}(S)}=1.
$$

Every pot is fully distributed. Thus the total charge is conserved.
 ∎

**Lemma P.**  At either apex of a bicone, the number of exactly-one-light triples is zero or two.

*Proof.*
Colour each base vertex by whether its pair with the apex is light. An apex triple is exactly-one-light if its two base vertices have different colours. Three vertices have either zero such pairs or two such pairs.
 ∎

There are at most four exactly-one-light triples in a bicone. An apex with any has an anchor, whose two base vertices have the same colour; it is both-light or both-heavy.

**Lemma Q.**  Suppose $H$ is avoiding, $\operatorname{CN}(x,y)=\{uv,vw,uw\}$, and

$$
L(xu)=\{v,w\},\qquad L(xw)=\{u,v\}.
$$

Let $T^\circ=x+uw$, $K=L(uw)$, $k=\vert K\vert$,

$$
a=|K\cap L(uv)|,\qquad b=|K\cap L(vw)|,\qquad
 e_z=[z\in L(uv)]+[z\in L(vw)]\quad(z\in K).
$$

Here brackets denote indicators. Then

- **(i)**  $s_{vw}=a$, $s_{uv}=b$, and $s_{xz}=1+e_z$ for $z\in K\setminus\{x\}$.

- **(ii)**

$$
c(T^\circ)=\frac1k+\frac1{2a}+\frac1{2b}
       +\sum_{z\in K\setminus\{x\}}\frac1{2(1+e_z)}-1.
$$

- **(iii)**  If $a=2$ or $b=2$, then $c(T^\circ)\geq1/6$, and $xy$ is the only triangle option of $T^\circ$.

*Proof.*
For (i), $xu\in\operatorname{CN}(v,w)$, so every member meets $xu$ by F1. A member $xr$ requires $xrw\in H$ and hence $r\in L(xw)\setminus\{v\}=\{u\}$. A member $ur$ belongs precisely when $r\in L(uv)\cap L(uw)$. Therefore

$$
\operatorname{CN}(v,w)=\{ur:r\in K\cap L(uv)\},\qquad s_{vw}=a.
$$

Exchanging $u,w$ gives $s_{uv}=b$. For $z\in K\setminus\{x\}$, the common link $\operatorname{CN}(x,z)$ contains $uw$, and every member meets $uw$. A member through $u$ is $uw$, or $uv$ if $z\in L(uv)$; a member through $w$ is $uw$, or $vw$ if $z\in L(vw)$. This gives $s_{xz}=1+e_z$. If $z=v$, then $e_z=0$ and the common link is just $\{uw\}$.

For (ii), $\sigma(T^\circ)=1/2+1/2+1/k$. Its options are $vw$ through $xu$, $uv$ through $xw$, and $xz$ through $uw$ for $z\in K\setminus\{x\}$. Apply (i).

For (iii), assume $a=2$; the other case exchanges $u,w$. The bicone edges put $x,y$ in $K\cap L(uv)\cap L(vw)$, so $K\cap L(uv)=\{x,y\}$. Thus $e_y=2$ and $e_z\leq1$ for $z\in K\setminus\{x,y\}$. Write $m_j$ for the number of those $z$ with $e_z=j$. Then $k=2+m_0+m_1$, $b=2+m_1$, and

$$
c(T^\circ)-\frac16=F:=\frac1{2+m_0+m_1}
 +\frac1{2(2+m_1)}+\frac{m_0}2+\frac{m_1}4-\frac34.
$$

At $(m_0,m_1)=(0,0),(1,0),(0,1),(0,2)$, the values are respectively $0,1/3,0,1/8$. In all other cases either $m_0\geq2$, or $m_1\geq3$, or both are positive, and
$F\geq m_0/2+m_1/4-3/4\geq0$.
Finally $\operatorname{CN}(v,w)$ has two members; $\operatorname{CN}(u,v)$ has common vertex $w$; and $\operatorname{CN}(x,z)\subseteq\{uw,uv,vw\}$ is triangular exactly when $e_z=2$, which here means $z=y$. Therefore $xy$ is the unique triangle option.
 ∎

### 6. The anchor condition and the global conclusion

#### 6.2 The condition G3h' and Theorem C'

The per-apex condition G3h' is the following statement: if apex $x$ of an active bicone $B_q$ has $d_x\geq1$ and its anchor $A_x$ is both-heavy, then

$$
\frac{c(A_x)}{\operatorname{act}(A_x)}\geq
       \sum_{T\in D_q,\ x\in T}\operatorname{def}(T).
$$

The denominator counts every active bicone containing the anchor; it is not assumed to equal one.

**Theorem C'.**  Suppose $H$ is avoiding, G1 holds at every deficient triple, and G3h' holds. Then Rule $2'$ leaves every triple with nonnegative final charge. Consequently $\Phi(H)\leq0$.

*Proof.*
By Lemma D, it suffices to consider deficient triples. G1(i) gives each such triple $T$ a unique triangle option $q$, hence a unique bicone $B_q$, which is active because it contains $T$. It receives only from this bicone. By G1(ii), it is exactly-one-light at its apex.

Fix an apex $x$ of $B_q$ with $d_x\geq1$. Every deficient triple there is exactly-one-light. Lemma P then gives exactly two exactly-one-light triples, so $d_x\leq2$ and the anchor $A_x$ exists. The anchor is not deficient: otherwise G1(i) would make $q$ its unique triangle option and G1(ii) would make it exactly-one-light, contrary to its definition. Thus the deficient triples at $x$ are among the other two triples and their deficit sum is the quantity $D$ used in Setting S below.

If the anchor is both-light, label it $A_x=x+uw$ with $xu,xw$ light and $xv$ heavy. The deficient triples at $x$ lie among $x+uv,x+vw$. If $x+uv$ is deficient, G1(iii) gives $s_{vw}=2$, so $a=2$ in Lemma Q. If $x+vw$ is deficient, its mirror gives $s_{uv}=2$, so $b=2$. At least one applies. Lemma Q therefore gives $c(A_x)\geq1/6$ and exactly one triangle option, whence $\operatorname{act}(A_x)=1$. By subdivision 2, every deficit is at most $1/12$, and hence

$$
\frac{c(A_x)}{\operatorname{act}(A_x)}\geq\frac16\geq\frac{d_x}{12}
 \geq\sum_{T\in D_q,\ x\in T}\operatorname{def}(T).
$$

If the anchor is both-heavy, the same final inequality is G3h'. In either case its right side is positive and $\operatorname{act}(A_x)\geq1$, so $c(A_x)>0$ and the anchor is a donor.

If both apexes have positive deficit, their anchors are distinct: each contains its own apex but not the other. Only apexes with positive deficit need an anchor contribution. Other donors contribute nonnegative amounts, and each deficient bicone member contains exactly one apex. Consequently

$$
\begin{aligned}
 \operatorname{pot}(q)
 &\geq\sum_{x:\,d_x\geq1}\frac{c(A_x)}{\operatorname{act}(A_x)}\\
 &\geq\sum_x\sum_{T\in D_q,\ x\in T}\operatorname{def}(T)
 =\sum_{S\in D_q}\operatorname{def}(S).
\end{aligned}
$$

The proportional split gives every $T\in D_q$ at least its own deficit. Its final charge is nonnegative. Finally conservation and F2 give

$$
0\leq\sum_{T\in H}\operatorname{final}(T)=\sum_{T\in H}c(T)=-\Phi(H).
$$

 ∎

G3h' is a sufficient per-apex condition for a bicone pot to cover its total deficit. Subdivisions 7 and 8 prove, for each both-heavy anchor in Setting S, the stronger inequality

$$
c(A)-\operatorname{act}(A)D>\frac1{k_{uw}}>0.
$$

Since $\operatorname{act}(A)\geq1$, this implies G3h'. Neither that estimate nor G1 uses Theorem C', so there is no circular dependence.

### 7. G3h' when $t_2(A)=1$ or $d_x=2$

#### 7.1 Setting S and notation

**Setting S.** Let $\operatorname{CN}(x,y)=\{uv,vw,uw\}$ be the bicone $B_q$, where $q=\{x,y\}$. The apex $x$ has exactly one light pair $xv$, so $L(xv)=\{u,w\}$ and $k_{xu},k_{xw}\ge3$. Its exactly-one-light triples are $T_1=x+uv$ and $T_2=x+vw$; its both-heavy anchor is $A=x+uw$. Let $D_x$ be the deficient triples among $T_1,T_2$, with $d_x=\vert D_x\vert \ge1$, and put

$$
D=\sum_{T\in D_x}\operatorname{def}(T).
$$

Every deficient triple of $H$ satisfies G1 by the unconditional Theorem G1 of Section 4. Setting S is exactly the both-heavy branch in step 4 of Theorem C': by Lemma P, the both-heavy anchor occurs if and only if exactly one apex-base pair at $x$ is light. By step 3 of Theorem C', G3h' in this setting reads $c(A)/\operatorname{act}(A)\ge D$.

The inputs are F1, Lemmas 1 and 2, the slot types, Theorem 1 (which gives $\operatorname{def}(T)\le1/12$, and hence $S_i\ge1$ below), and (E3) from Section 2; Lemma 1g(a), identifying triangle options with type-2 slots; and Theorem G1 and Corollary 6g from Section 4.

Write $P=L(uv)$, $Q=L(vw)$, $M=L(uw)$, $X_u=L(xu)$ and $X_w=L(xw)$. The bicone gives $x,y\in P\cap Q\cap M$, $v,w\in X_u$, and $u,v\in X_w$.

*Slot model of $A=\{x,u,w\}$.* The groups are

$$
\mathcal A=M\setminus\{x\},\qquad
 \mathcal B=X_w\setminus\{u\},\qquad
 \mathcal C=X_u\setminus\{w\}.
$$

Their options are, respectively, $\{x,z\}$ through $uw$, $\{u,z\}$ through $xw$, and $\{w,z\}$ through $xu$. The relation $R_u$ joins $\mathcal C$ and $\mathcal A$, with $z'\sim z$ if and only if $uz'z\in H$; $R_w$ joins $\mathcal A$ and $\mathcal B$ via $w$; and $R_x$ joins $\mathcal B$ and $\mathcal C$ via $x$. An $R_x$ edge of $A$ means an edge of this last relation. Let $\mathcal A_u$, $\mathcal A_w$, and $\mathcal A_0$ be the slots of $\mathcal A$ that are type 1 in $R_u$, type 1 in $R_w$, and isolated, respectively. Put

$$
\begin{aligned}
 U&=\frac1{|X_u|}+\sum_{\substack{s\in\mathcal C\\s\text{ not type 2}}}\operatorname{cost}(s)
       +\sum_{s\in\mathcal A_u}\operatorname{cost}(s),\\
 W&=\frac1{|X_w|}+\sum_{\substack{s\in\mathcal B\\s\text{ not type 2}}}\operatorname{cost}(s)
       +\sum_{s\in\mathcal A_w}\operatorname{cost}(s),
\end{aligned}
$$

where $\operatorname{cost}(s)=1/(2(1+d(s)))$ and $d(s)$ is the degree of $s$ in $A$. For $i=1,2$ put $S_i=c(T_i)+13/12$. Thus $\operatorname{def}(T_i)=13/12-S_i$ when $T_i$ is deficient, and $S_i\ge1$ by Theorem 1 of Section 2.

*Slot model of $T_1=\{x,u,v\}$.* Apply Corollary 6g with $a=x$, $b=v$, $c=u$. Its groups are $A_1=P\setminus\{x\}$, with options $\{x,z\}$; $B_1=X_u\setminus\{v\}$, with options $\{v,z\}$ through $xu$; and $C_1=L(xv)\setminus\{u\}=\{w\}$. The $u$-relation joins $A_1$ and $B_1$, with $z\sim s$ if and only if $uzs\in H$; the $v$-relation joins $C_1$ and $A_1$; the $x$-relation joins $B_1$ and $C_1$. The triple $T_2=\{x,v,w\}$ is the mirror under $u\leftrightarrow w$, exchanging $P\leftrightarrow Q$, $X_u\leftrightarrow X_w$, $R_u\leftrightarrow R_w$ and $\mathcal C\leftrightarrow\mathcal B$. Every statement below has this mirror.

#### 7.2 Structure of the anchor

**Lemma S1.** In setting S:

- **(a)**  $s_{uw}=2$. Hence $P\cap Q=\{x,y\}$ and $X_u\cap X_w=\{v\}$.

- **(b)**  The slot $y\in\mathcal A$ is type 2. Its only $R_u$-neighbour is the slot $v$ of $\mathcal C$, and its only $R_w$-neighbour is the slot $v$ of $\mathcal B$.

- **(c)**  The $R_u$-neighbours of $v\in\mathcal C$ are $y$ and the slots of $J_1=(P\cap M)\setminus\{x,y\}$; this slot has no $R_x$ neighbour. In the mirror, $v\in\mathcal B$ has $R_w$-neighbours $y$ and $J_2=(Q\cap M)\setminus\{x,y\}$, and no $R_x$ neighbour.

- **(d)**  The only type-2 slot of $\mathcal A$ is $y$; every slot of $J_1$ belongs to $\mathcal A_u$, and every slot of $J_2$ to $\mathcal A_w$.

- **(e)**  The triangle options of $A$ are precisely the options of its type-2 slots; one is $q=\{x,y\}$.

*Proof.* (a) Some $T_i$ is deficient. For $T_1=x+uv$, Theorem G1(iii) applied to its light pair $xv$ gives $L(xv)=\{u,w\}$ and $s_{uw}=2$. For $T_2=x+vw$, exchange $u,w$ to obtain $s_{wu}=2$. Since $xvu,xvw\in H$, we have $xv\in\operatorname{CN}(u,w)$. By F1 every member meets $xv$. A member $vz$, with $z\notin\{u,w\}$, requires $uvz,wvz\in H$, or $z\in P\cap Q$; a member $xz$ requires $z\in X_u\cap X_w$. The edge $xv$ is the only member of both kinds. Therefore

$$
s_{uw}=|P\cap Q|+|X_u\cap X_w|-1.
$$

Together with $x,y\in P\cap Q$ and $v\in X_u\cap X_w$, this proves (a).

(b) The bicone triple $y+uv$ gives $uyv\in H$, and $v\in\mathcal C$, so $y\sim v$ in $R_u$. Likewise $wyv\in H$ and $v\in\mathcal B$, so $y\sim v$ in $R_w$. Lemma 2 makes these its only neighbours.

(c) An $R_u$-neighbour of $v\in\mathcal C$ is $z\in M\setminus\{x\}$ with $uvz\in H$, equivalently $z\in(P\cap M)\setminus\{x\}=\{y\}\cup J_1$. An $R_x$-neighbour would be $b\in\mathcal B$ with $xvb\in H$, so $b\in L(xv)=\{u,w\}$. But $u\notin\mathcal B$ and $w\notin X_w$.

(d) A type-2 slot $z\in\mathcal A$ has neighbours that are slots of one vertex $s\in\mathcal C\cap\mathcal B\subseteq X_u\cap X_w=\{v\}$. Thus $uzv,wzv\in H$, and $z\in(P\cap Q)\setminus\{x\}=\{y\}$. A slot $z\in J_1$ is $R_u$-adjacent to $v\in\mathcal C$ by (c), and is not type 2, so it is type 1 in $R_u$.

(e) For a slot $s$ of a triple $T$, $s_{q_s}=1+d(s)$, and $\operatorname{CN}(q_s)$ consists of the pair of $T$ through which $q_s$ passes and one pair per neighbour of $s$ (Lemma 1 and its proof). If $s$ is type 1, these pairs all contain one common vertex of $T$, the apex of its relation, so $\operatorname{CN}(q_s)$ is not a triangle. If $s$ is isolated, $s_{q_s}=1$. If $s$ is type 2, $\operatorname{CN}(q_s)$ is a triangle by Lemma 2. The option of $y$ is $q$. $\square$

**Lemma S2 (decomposition).**

$$
c(A)=\frac1{k_{uw}}+\frac{t_2(A)}6+\frac{|\mathcal A_0|}2+U+W-2,
$$

where $t_2(A)$ counts the type-2 slots of $A$.
*Proof.* We have $\sigma(A)=1/\vert M\vert +1/\vert X_u\vert +1/\vert X_w\vert$. By Lemma S1(d), the slots of $\mathcal A$ are $y$, of cost $1/6$; $\mathcal A_u$; $\mathcal A_w$; and $\mathcal A_0$, each of cost $1/2$. Every slot of $\mathcal B$ and $\mathcal C$ is either type 2, of cost $1/6$, or counted in $W$ and $U$, respectively. $\square$

#### 7.3 The $u$-side when $T_1$ is deficient

Let $r=\vert X_u\vert -2\ge1$, since $X_u\supseteq\{v,w\}$ and $k_{xu}\ge3$, and $R=X_u\setminus\{v,w\}$. Thus $\mathcal C=\{v\}\cup R$ and $B_1=\{w\}\cup R$. Set $j=\vert J_1\vert$, $D_1=P\setminus(\{x,y\}\cup J_1)$ and $d=\vert D_1\vert$, so $\vert P\vert =2+j+d$. Set $E_u=\mathcal A_u\setminus J_1$ and $e=\vert E_u\vert$.

**Lemma S3 ($T_1$ side).** If $T_1$ is deficient, then

$$
\begin{aligned}
 S_1\ge{}&\frac1{2+j+d}+\frac1{2+r}+\frac1{2(2+j)}
       +\sum_{z\in J_1}\frac1{2(1+d_A(z))}\\
       &+\frac d{2(1+r)}+\frac r{2(1+j+d)},
\end{aligned}
$$

where $d_A(z)$ is the degree of $z\in J_1$ in $A$.
*Proof.* Use Corollary 6g with $a=x$, $b=v$, $c=u$, type-2 slot $(y,A_1)$, partner $w$, and $C_1=\{w\}$. The $v$-relation of $T_1$ is the single edge $(w,y)$; the $x$-relation is empty; every other slot is isolated or type 1 in the $u$-relation. Corollary 6g says type 1, but only the upper bounds below are used. Thus $\sigma(T_1)=1/\vert P\vert +1/\vert X_u\vert +1/2$. The slot $w\in C_1$ costs $1/4$, having degree 1; $y$ costs $1/6$; every other slot $s$ costs $1/(2(1+d_1(s)))$, where $d_1(s)$ is its $u$-relation degree. Since $1/2+1/4+1/6=11/12$, $S_1$ equals $1/\vert P\vert +1/\vert X_u\vert$ plus the costs over $A_1\setminus\{y\}$ and $B_1$.

The neighbours of $w\in B_1$ are $z\in P\setminus\{x\}$ with $uwz\in H$, namely $(P\cap M)\setminus\{x\}=\{y\}\cup J_1$, so its degree is exactly $1+j$. A slot $z\in J_1$ has neighbours $s\in X_u\setminus\{v\}$ with $uzs\in H$: the slot $w$, because $z\in M$, and $N_u(z)\cap R$. In $A$, its $R_u$-neighbours are the slots $s\in X_u\setminus\{w\}$ with $uzs\in H$, namely $v$, because $z\in P$, and $N_u(z)\cap R$. It has no $R_w$ neighbour by Lemma S1(d). Consequently $d_1(z)=d_A(z)$. A slot $z\in D_1$ is not adjacent to $w$, because $z\notin M$, so $d_1(z)\le r$. A slot $s\in R$ is not adjacent to $y$: the latter's only neighbour in $B_1$ is $w$, by Lemma 2 in $T_1$. Hence $d_1(s)\le j+d$. Costs decrease with degree. $\square$

**Lemma S4 (anchor $u$-side, no $R_x$ edge).** If $A$ has no $R_x$ edge, then

$$
\begin{aligned}
 U\ge{}&\frac1{2+r}+\frac1{2(2+j)}+\sum_{z\in J_1}\frac1{2(1+d_A(z))}\\
 &+\frac e{2(1+r)}+\frac r{2(1+j+e)}.
\end{aligned}
$$

*Proof.* Without $R_x$ edges every slot of $\mathcal C$ has only $R_u$ edges, so none is type 2. Thus $U$ is $1/\vert X_u\vert$ plus the costs over $\mathcal C$ and $\mathcal A_u$. The slot $v$ costs $1/(2(2+j))$ by Lemma S1(c). A slot of $R$ has its $R_u$-neighbours in $\mathcal A_u$: not $y$, by Lemma S1(b), and every $\mathcal A$-slot with an $R_u$ edge but no $R_w$ edge belongs to $\mathcal A_u$. Its degree is therefore at most $j+e$. A slot $z\in E_u$ is not in $P$, since otherwise $z\in(P\cap M)\setminus\{x\}=\{y\}\cup J_1$. It is not adjacent to $v$, so its degree is at most $r$. $\square$

**Lemma S5 (joint inequality).** For integers $j,d,e\ge0$ and $r\ge1$,

$$
\begin{aligned}
 \Psi(j,d,e,r):={}&\frac2{r+2}+\frac1{j+d+2}+\frac1{2+j}+\frac j{r+2}\\
 &+\frac d{2(1+r)}+\frac e{2(1+r)}
   +\frac r{2(1+j+d)}+\frac r{2(1+j+e)}>2.
\end{aligned}
$$

*Proof.* Put $P_d=1+j+d$ and $P_e=1+j+e$.

If $r\ge j$, use $d=P_d-1-j$ and $r=(r+1)-1$ to obtain

$$
\begin{aligned}
 \frac d{2(1+r)}+\frac r{2P_d}
 &=\left[\frac{P_d}{2(r+1)}+\frac{r+1}{2P_d}\right]
    -\frac{1+j}{2(1+r)}-\frac1{2P_d}\\
 &\ge1-\frac{1+j}{2(1+r)}-\frac1{2P_d}
\end{aligned}
$$

by AM–GM, and similarly for $e$. Since
$(2+j)/(r+2)-(1+j)/(r+1)=(r-j)/((r+1)(r+2))$, it follows that

$$
\begin{aligned}
 \Psi\ge2+\frac{r-j}{(r+1)(r+2)}
 +\left[\frac1{P_d+1}-\frac1{2P_d}\right]
 +\left[\frac1{2+j}-\frac1{2P_e}\right].
\end{aligned}
$$

The second bracket is $(P_d-1)/(2P_d(P_d+1))\ge0$. Since $P_e\ge1+j$, the third is at least $j/(2(1+j)(2+j))\ge0$. If $r>j$, the first term after 2 is positive; if $r=j\ge1$, the third bracket is positive. Thus $\Psi>2$.

If $j\ge r+1$, then for real $e\ge0$,

$$
\frac{d}{de}\left[\frac e{2(1+r)}+\frac r{2(1+j+e)}\right]
 =\frac1{2(1+r)}-\frac r{2P_e^2}>0,
$$

since $P_e\ge r+2$ and $(r+2)^2>r(r+1)$. This sum is at least $r/(2(1+j))$. For real $d\ge0$, set $\psi(d)=1/(2+j+d)+d/(2(1+r))+r/(2(1+j+d))$. Its derivative

$$
-\frac1{(P_d+1)^2}+\frac1{2(1+r)}-\frac r{2P_d^2}
$$

is increasing in $P_d$. At $P_d=r+2$ it is

$$
\frac{3r+4}{2(r+1)(r+2)^2}-\frac1{(r+3)^2}>0,
$$

because $(3r+4)(r+3)^2-2(r+1)(r+2)^2=r^3+12r^2+35r+28>0$. Thus $\psi(d)\ge\psi(0)=1/(2+j)+r/(2(1+j))$, and

$$
\Psi\ge\chi(\ell):=\frac{\ell+1}{r+2}+\frac2{\ell+1}+\frac r\ell,
 \qquad \ell=j+1\ge r+2.
$$

The derivative $\chi'(\ell)=1/(r+2)-2/(\ell+1)^2-r/\ell^2$ is increasing in $\ell$, and $\chi'(r+2)=2/(r+2)^2-2/(r+3)^2>0$. Therefore

$$
\chi(\ell)\ge\chi(r+2)=\frac{2r+3}{r+2}+\frac2{r+3}
 =2+\frac{r+1}{(r+2)(r+3)}>2.
$$

$\square$

**Corollary ($u$-side, $T_1$ deficient, no $R_x$ edge).** $U+S_1>2$.
*Proof.* Add Lemmas S3 and S4. The $J_1$-terms appear twice with the same degrees $d_A(z)\le1+r$, and hence contribute at least $2j/(2(2+r))=j/(r+2)$. The sum is at least $\Psi(j,d,e,r)>2$ by Lemma S5. $\square$

#### 7.4 The $u$-side when $T_1$ is not deficient

**Lemma S6 (one-group bound).** For integers $a\ge0$ and $c\ge2$,

$$
f(a,c):=\frac1{1+c}+\frac1{2(2+a)}+\frac{c-1}{2(1+a)}+\frac a{2(1+c)}\ge\frac{11}{12},
$$

with equality only at $(a,c)=(1,2)$.
*Proof.* AM–GM gives

$$
\begin{aligned}
 f&=\left[\frac{a+2}{2(c+1)}+\frac{c+1}{2(a+1)}\right]-\frac1{a+1}+\frac1{2(a+2)}\\
 &\ge\sqrt{\frac{a+2}{a+1}}-\frac1{a+1}+\frac1{2(a+2)}.
\end{aligned}
$$

For $t=1/(a+1)\in(0,1]$, $\sqrt{1+t}\ge1+t/2-t^2/8$: squaring the right-hand side gives $1+t-t^3/8+t^4/64\le1+t$. Thus

$$
f\ge1-\frac1{2(a+1)(a+2)}-\frac1{8(a+1)^2}.
$$

For $a\ge2$, this is at least $1-1/24-1/72=17/18>11/12$. For $a=0$, $f(0,c)=1/(1+c)+1/4+(c-1)/2\ge13/12$. For $a=1$, $f(1,c)=3/(2(1+c))+(c-1)/4+1/6$ equals $11/12$ at $c=2$, and $f(1,c+1)-f(1,c)=1/4-3/(2(1+c)(2+c))>0$ for $c\ge2$. $\square$

**Corollary ($u$-side, no $R_x$ edge).** If $A$ has no $R_x$ edge, then $U\ge11/12$.
*Proof.* Let $c=\vert \mathcal C\vert =r+1\ge2$, since $xu$ is heavy in setting S and $\vert \mathcal C\vert =k_{xu}-1\ge2$. Set $a=\vert \mathcal A_u\vert$. The slot $v$ has degree $1+j\le1+a$, since $J_1\subseteq\mathcal A_u$. Each slot of $R$ has degree at most $a$ by the proof of Lemma S4, and each slot of $\mathcal A_u$ has degree at most $c$. Hence $U\ge f(a,c)\ge11/12$. $\square$

The mirror statement $W\ge11/12$ uses $\vert \mathcal B\vert =k_{xw}-1\ge2$.

#### 7.5 Theorem S1 and Proposition S2

**Theorem S1.** In setting S, if $A$ has no $R_x$ edge, then $t_2(A)=\operatorname{act}(A)=1$ and

$$
c(A)-D\ge\frac1{k_{uw}}+\frac{|\mathcal A_0|}2+\text{positive terms}>0.
$$

In particular G3h' holds and $A$ is not deficient.
*Proof.* Without $R_x$ edges, no slot of $\mathcal B$ or $\mathcal C$ is type 2: their two relations are $R_w,R_x$ and $R_u,R_x$, respectively. Lemma S1(d),(e) therefore makes $q$ the only triangle option, so $t_2(A)=1$. The bicone $B_q$ is active and contains $A$, so $\operatorname{act}(A)=1$. Lemma S2 gives

$$
c(A)=\frac1{k_{uw}}+\frac16+\frac{|\mathcal A_0|}2+U+W-2.
$$

If $T_1$ is deficient, $\operatorname{def}(T_1)=13/12-S_1$, and likewise for $T_2$. If $d_x=2$, then

$$
\begin{aligned}
 c(A)-\operatorname{def}(T_1)-\operatorname{def}(T_2)
 &=\frac1{k_{uw}}+\frac{|\mathcal A_0|}2+(U+S_1-2)+(W+S_2-2)\\
 &>\frac1{k_{uw}},
\end{aligned}
$$

by the corollary of Section 7.3 and its mirror. If $d_x=1$ and $T_1$ is deficient, then

$$
\begin{aligned}
 c(A)-\operatorname{def}(T_1)
 &=\frac1{k_{uw}}+\frac{|\mathcal A_0|}2+(U+S_1-2)+(W-11/12)\\
 &>\frac1{k_{uw}},
\end{aligned}
$$

by Section 7.3 and the mirror of Section 7.4. The case with $T_2$ deficient is its mirror. $\square$

**Proposition S2.** Put $t=t_2(A)$. We have $\operatorname{act}(A)\le t$, because it counts active bicones among the $t$ triangle options (Lemma S1(e)), and $D\le d_x/12\le1/6$ by Theorem 1 of Section 2. Lemma S2 gives

$$
\begin{aligned}
 c(A)-\operatorname{act}(A)D&\ge c(A)-tD\\
 &=\left[\frac1{k_{uw}}+\frac16+\frac{|\mathcal A_0|}2+U+W-2-D\right]
    +(t-1)(1/6-D).
\end{aligned}
$$

The last term is nonnegative. Thus G3h' holds as soon as

$$
(\star)\qquad \frac1{k_{uw}}+\frac16+\frac{|\mathcal A_0|}2+U+W-2\ge D,
$$

where $U,W$ exclude the type-2 slots of $\mathcal C,\mathcal B$. In general the slack $(t-1)(1/6-D)$ is only known to be nonnegative. The stronger bound $(t-1)/12$ holds only when $d_x=1$, since then $D\le1/12$; it is not used. $\square$

Theorem S1 establishes $(\star)$ when there are no $R_x$ edges.

#### 7.6 Anchors with an $R_x$ edge: two structural lemmas

**Lemma S8 (type-2 slots of $\mathcal C$ and their bicones).** Let $R_2$ be the type-2 slots of $\mathcal C$. Every deficient triple of $H$ satisfies G1.

- **(a)**  All slots of $R_2$ have one common partner $z^*\in(M\cap X_w)\setminus\{x,u,v\}$, and $z^*\notin X_u$.

- **(b)**  If $\vert R_2\vert \ge2$, no bicone $B_{q_r}$, for $r\in R_2$, is active.

- **(c)**  Consequently $\operatorname{act}(A)\le1+[\vert R_2\vert =1]+[\vert R'_2\vert =1]$, where $R'_2$ is the mirror set of type-2 slots of $\mathcal B$.

*Proof.* (a) A type-2 slot $r\in\mathcal C$ has $R_u$- and $R_x$-neighbours that are slots of one vertex $z$, its partner. Then $z\in\mathcal A\cap\mathcal B$, so $urz,xrz\in H$ and $rz\in\operatorname{CN}(u,x)$. Every $s\in\mathcal A\cap\mathcal B$ has $uws,xws\in H$, giving $ws\in\operatorname{CN}(u,x)$. By F1, $ws$ meets $rz$, so $\mathcal A\cap\mathcal B\subseteq\{r,z\}$. If a second type-2 slot $r'$ had partner $z'\ne z$, then $z'\in\mathcal A\cap\mathcal B\subseteq\{r,z\}$ gives $z'=r$. This would imply $r\in\mathcal A\cap\mathcal B\cap\mathcal C\subseteq X_u\cap X_w=\{v\}$, but $v\in\mathcal C$ has no $R_x$ edge by Lemma S1(c), and is not type 2. Hence there is one common partner $z^*$. Its slots in $\mathcal A$ and $\mathcal B$ give $z^*\in M\cap X_w$ and $z^*\notin\{x,u\}$. Also $z^*\ne v$, because $v\in\mathcal B$ has no $R_x$ edge. Since $X_u\cap X_w=\{v\}$, we have $z^*\notin X_u$.

(b) For $r\in R_2$, $q_r=\{w,r\}$ and $\operatorname{CN}(w,r)=\{xu,uz^*,xz^*\}$ by Lemmas 1 and 2. The six bicone triples are

$$
A=w+xu,\quad w+uz^*,\quad w+xz^*,\quad
 r+xu,\quad r+uz^*,\quad r+xz^*.
$$

The triple $A$ has at least three triangle options, from $y$ and two slots of $R_2$. Both $w+uz^*$ and $w+xz^*$ have triangle options $\{w,r'\}$ for every $r'\in R_2$: each $r'$ lies in $L(uz^*)\cap L(xz^*)$, and $\operatorname{CN}(w,r')$ is a triangle. Thus none of these first three triples is deficient, by G1(i).

Suppose $T=r+p_1p_2$ is deficient, where $\{p_1,p_2,p_3\}=\{x,u,z^*\}$. By G1 its only triangle option is $\{r,w\}$. Apply Corollary 6g with $a=r$, light pair $ab=rp_1$ (say), $c=p_2$, and partner $p_3$ of the type-2 slot $w\in L(p_1p_2)\setminus\{r\}$. The $b$-relation of $T$ joins the slot $p_3$ to slots $s\in L(p_1p_2)\setminus\{r\}$ when $p_1p_3s\in H$, and must be the single edge to $w$.
The six relabellings are written out in Appendix [Expanded structural and accounting arguments](#expanded-structural-and-accounting-arguments), part C.
But any $r'\in R_2\setminus\{r\}$ satisfies $r'\in L(p_1p_2)$ and $p_1p_3r'\in H$, since $xur',uz^*r',xz^*r'\in H$: here $r'\in X_u$, and its $R_u$ and $R_x$ edges go to $z^*$. Also $r'\notin\{r,p_3\}$, since $r'\in X_u$ and $z^*\notin X_u$. This is a contradiction.

(c) The number $\operatorname{act}(A)$ counts the bicone of $y$ and active bicones of type-2 slots in $\mathcal C$ and $\mathcal B$. Part (b) permits at most one from each group, and only when that group has exactly one type-2 slot. $\square$

Writing $a_* = \operatorname{act}(A)$ for this display, the slack in Proposition S2 improves to

$$
c(A)-a_*D\ge\bigl(\text{left side of }(\star)-D\bigr)
       +\frac{t-a_*}{6}+(a_*-1)(1/6-D).
$$

#### 7.7 Classes with $R_x$ edges, caps, and $\Psi_N$

Split $R=\mathcal C\setminus\{v\}$ into $R_U$ (type 1 in $R_u$), $R_X$ (type 1 in $R_x$), $R_0$ (isolated in $A$), and $R_2$ (type 2). Put

$$
k=|R_U|,\quad q=|R|-k,\quad r=k+q=|X_u|-2,\quad r_2=|R_2|.
$$

In the mirror, $R'=\mathcal B\setminus\{v\}=R'_W\cup R'_X\cup R'_0\cup R'_2$. Define

$$
U^-=U-\sum_{s\in R_X\cup R_0}\operatorname{cost}(s),
$$

and define $W^-$ by the mirror. The set $R_2$ is not included in $U$.
The degree caps in $A$ are as follows.

-  A slot $z\in J_1$ has $R_u$-neighbours $v$ and slots of $R_U\cup R_2$. A slot of $R_2$ has only $z^*$ as its $R_u$-neighbour by Lemma S8(a). Thus $d_A(z)\le1+k$ for $z\ne z^*$, and $d_A(z^*)\le1+k+r_2$.

-  A slot of $E_u$ has degree at most $k$, except $z^*$, whose degree is at most $k+r_2$. A slot of $R_U$ has degree at most $j+e$, with no $R_x$ edge.

-  The slot $v$ costs $1/(2(2+j))$, since Lemma S1(c) is independent of $R_x$.

If $k=0$, then $E_u\subseteq\{z^*\}$. Lemma S3, concerning only $T_1$, is unchanged. With $P_d=1+j+d$ and $P_e=1+j+e$, it gives

$$
U^-+S_1\ge\Psi_N(j,d,e,k,q)-L^*,
$$

where

$$
\begin{aligned}
 \Psi_N:={}&\frac2{2+r}+\frac1{P_d+1}+\frac1{2+j}+\frac j{2+k}\\
 &+\frac d{2(1+r)}+\frac r{2P_d}+\frac e{2(1+k)}+\frac k{2P_e},
\end{aligned}
$$

and

$$
L^*=\begin{cases}
 0,&R_2=\varnothing,\\
 \dfrac1{2+k}-\dfrac1{2+k+r_2},&z^*\in J_1,\\[3pt]
 \dfrac1{2(1+k)}-\dfrac1{2(1+k+r_2)},&z^*\in E_u.
 \end{cases}
$$

The $J_1$ case has two copies of the exceptional cost, in $T_1$ and in $A$.

#### 7.8 Lemmas S9, S10.1, S10, and S11

**Lemma S9 (size of the shared row set).** If $T_1$ is deficient, then $j\ge2$. If also $r\ge j$, then $j\ge5$ and $S_1-1\ge1/(2(2+j))$.
*Proof.* In Lemma S3 use $d_A(z)\le1+r$ for every $z\in J_1$. The pairing from Lemma S5 gives

$$
\frac d{2(1+r)}+\frac r{2P_d}\ge1-\frac{1+j}{2(1+r)}-\frac1{2P_d},
$$

so

$$
S_1\ge1+\frac1{2(2+j)}+\frac{P_d-1}{2P_d(P_d+1)}
                   +\frac{r-j}{2(1+r)(2+r)}.
$$

If $r\ge j$, the inequality $S_1<13/12$ forces $1/(2(2+j))<1/12$, hence $j\ge5$. If $r<j$, then $j\ge2$ because $r\ge1$. $\square$

**Lemma S10.1 (three case bounds for $\Psi_N$).** These bounds are also used by Lemma U(c). Suppose $T_1$ is deficient, so $j\ge2$, and $j\ge5$ if $r\ge j$, by Lemma S9.

- **(i)**  If $k\ge j$, then

$$
\begin{aligned}
 \Psi_N-2\ge{}&\frac{r-j}{2(1+r)(2+r)}+\frac{k-j}{2(1+k)(2+k)}
              +\frac{(j-2)q}{2(2+r)(2+k)}\\
 &+\frac{P_d-1}{2P_d(P_d+1)}+\frac j{2(1+j)(2+j)}>0.
\end{aligned}
$$

- **(ii)**  If $k<j\le r$, so $j\ge5$, then

$$
\Psi_N-2\ge\frac k{(k+2)(k+3)}+\frac{P_d-1}{2P_d(P_d+1)}>0.
$$

  For $k=0$ we also have $\Psi_N-2\ge10/7$.

- **(iii)**  If $j\ge r+1$, then

$$
\Psi_N\ge\chi(j+1)+(r-k)\left[\frac j{(2+k)(2+r)}-\frac1{2(1+j)}\right],
$$

  where $\chi$ is from Lemma S5. The bracket is at least
$(r+1)/((2+k)(2+r))-1/(2(r+2))\ge0$, and
$\chi(j+1)-2\ge(r+1)/((r+2)(r+3))>0$.

The cases cover all $k,j,r$, so $\Psi_N>2$ throughout.

*Proof.* (i) Pair the $d$-terms with $r+1$ and the $e$-terms with $k+1$ as in Lemma S5, using

$$
\begin{aligned}
 &\frac2{2+r}+\frac j{2+k}-\frac{1+j}{2(1+r)}-\frac{1+j}{2(1+k)}\\
 &\qquad=\frac{r-j}{2(1+r)(2+r)}+\frac{k-j}{2(1+k)(2+k)}
              +\frac{(j-2)q}{2(2+r)(2+k)}.
\end{aligned}
$$

All terms in the asserted bound are nonnegative, since $r\ge k\ge j\ge2$, and its last term is positive.

(ii) For real $e\ge0$, $e/(2(1+k))+k/(2P_e)$ is increasing, since $P_e\ge k+2$, and is at least $k/(2(1+j))$. The $d$-pairing gives

$$
\Psi_N\ge1+f+\frac{P_d-1}{2P_d(P_d+1)}.
$$

Here

$$
f=\frac2{2+r}+\frac1{2+j}+\frac j{2+k}+\frac k{2(1+j)}-\frac{1+j}{2(1+r)}.
$$

Since $j\ge3$, $df/dr\ge(-2+(1+j)/2)/(1+r)^2\ge0$. Thus $f\ge g_{10}(j)-1/2$, where

$$
g_{10}(j)=\frac j{2+k}+\frac k{2(1+j)}+\frac3{2+j}.
$$

For $j\ge k+1$,

$$
g_{10}'(j)\ge\frac{k+4}{2(k+2)^2}-\frac3{(k+3)^2}>0,
$$

since $(k+4)(k+3)^2-6(k+2)^2=k^3+4k^2+9k+12$. Consequently $g_{10}(j)\ge g_{10}(\max(k+1,5))$. Using
$g_{10}(k+1)-3/2=k/((k+2)(k+3))$ gives the asserted bound; its last term is positive because $P_d\ge6$. When $k=0$, we have $\Psi_N-2\ge g_{10}(5)-3/2=10/7$.

(iii) The $e$-terms are at least $k/(2(1+j))$ as in (ii). The $d$-terms, together with $1/(P_d+1)$, are minimised at $d=0$ by Lemma S5 in the case $j\ge r+1$. Thus

$$
\Psi_N\ge\chi(j+1)+(r-k)\left[\frac j{(2+k)(2+r)}-\frac1{2(1+j)}\right].
$$

The bracket is at least $(r+1)/((2+k)(2+r))-1/(2(r+2))\ge0$, because $j\ge r+1$ and $k\le r$. Lemma S5 also gives $\chi(j+1)-2\ge(r+1)/((r+2)(r+3))>0$. $\square$

**Lemma S10 (LD).** If $T_1$ is deficient, then $U^-+S_1+\sigma_u>2$, where

$$
\sigma_u=\begin{cases}0,&r_2=0,\\S_1-1,&r_2=1,\\1/3,&r_2\ge2.\end{cases}
$$

*Proof.* Section 7.7 gives $U^-+S_1\ge\Psi_N-L^*$. If $R_2=\varnothing$, then $L^*=0$, and Lemma S10.1 gives $\Psi_N>2$. Otherwise $z^*$ exists and $r_2\ge1$.

If $r_2\ge2$, then $\sigma_u=1/3$. For $k\ge1$, $L^*<1/(2+k)\le1/3$. For $k=0$ we have $k<j$. In case (ii), $\Psi_N-2\ge10/7>L^*$. In case (iii), the bracket is at least $r/(2(r+2))$, so $\Psi_N-2\ge r^2/(2(r+2))\ge1/6$, and $1/6+1/3=1/2>L^*$.

Now suppose $r_2=1$, so $\sigma_u=S_1-1$. We have

$$
L^*\le\frac1{(2+k)(3+k)}\quad(z^*\in J_1),\qquad
 L^*\le\frac1{2(1+k)(2+k)}\quad(z^*\in E_u).
$$

In case (i), $r\ge k\ge j$, and Lemma S9 gives

$$
\sigma_u\ge\frac1{2(2+j)}\ge\frac1{(2+j)(3+j)}\ge L^*,
$$

for both forms of $L^*$, since $k\ge j$.

In case (ii), for $k\ge1$, $k/((k+2)(k+3))\ge L^*$. For the $E_u$ form this follows from $2k(k+1)\ge k+3$. If equality occurs in either form at $k=1$, the positive term $(P_d-1)/(2P_d(P_d+1))$ in Lemma S10.1(ii) supplies strictness. For $k=0$, $10/7>L^*$. In both subcases $\sigma_u=S_1-1\ge0$ by Theorem 1 of Section 2.

In case (iii), first let $z^*\in J_1$. Set $m=r-k\ge1$, since $q\ge r_2=1$, and note $2+k\le r+1$. Then

$$
\Psi_N-\chi(j+1)\ge\frac m{2(r+2)}\ge\frac1{(2+k)(3+k)}.
$$

The second inequality follows from $h(m)=m(r+2-m)(r+3-m)\ge2(r+2)$ for $1\le m\le r$: the function is unimodal on $[0,r+2]$, and $h(1)=(r+1)(r+2)$, $h(r)=6r$.

Finally, in case (iii) with $z^*\in E_u$, we have $e\ge1$. The $e$-terms are at least

$$
\begin{aligned}
 \frac{e-1}{2(1+k)}+\frac1{2(2+k)}+\frac k{2P_e}
 &\ge\frac1{2(2+k)}+\frac k{2(2+j)}\\
 &\ge\frac k{2(1+j)}.
\end{aligned}
$$

Here the expression increases in $e$, and $(1+j)(2+j)\ge k(2+k)$. Thus the case (iii) bound holds with $L^*$ already included.
The reduced exceptional-cost calculation is written out in Appendix [Expanded structural and accounting arguments](#expanded-structural-and-accounting-arguments), part D.
In both subcases $\sigma_u=S_1-1\ge0$ by Theorem 1 of Section 2. $\square$

**Lemma S11 (one side, $R_x$ edge, no type-2 slot in $\mathcal B\cup\mathcal C$).** If $A$ has an $R_x$ edge and $R_2=R'_2=\varnothing$, then

$$
U+\sum_{s\in R'_X}\operatorname{cost}(s)\ge11/12.
$$

*Proof.* Every $R_x$ edge joins $R_X$ to $R'_X$, since there is no type-2 slot in $\mathcal B\cup\mathcal C$ and the $v$-slots have no $R_x$ edge. Hence $r_X=\vert R_X\vert \ge1$ and $r'_X=\vert R'_X\vert \ge1$. Slots of $R_X$ have degree at most $r'_X$, and slots of $R'_X$ at most $r_X$. By (E3), their total cost is at least

$$
\begin{aligned}
 \frac{r_X}{2(1+r'_X)}+\frac{r'_X}{2(1+r_X)}
 &\ge1-\frac1{2(1+r_X)}-\frac1{2(1+r'_X)}\\
 &\ge\frac34-\frac1{2(1+r_X)}.
\end{aligned}
$$

For the rest of $U$, if $k\ge1$, the slots $v,R_U,\mathcal A_u$ have degree caps $1+a,a,1+k$, respectively, where $a=\vert \mathcal A_u\vert$. Their cost is at least $f(a,1+k)-1/(2+k)\ge11/12-1/3$, by Lemma S6. Therefore

$$
U+\sum_{s\in R'_X}\operatorname{cost}(s)\ge11/12-1/3+3/4-1/4=13/12.
$$

If $k=0$, then $\mathcal A_u$ consists of $J_1$, each slot having degree 1, and this part costs at least $1/(2(2+j))+j/4\ge1/4$. Also $1/\vert X_u\vert \ge1/(2+r_X+r_0)$, and $R_0$ costs $r_0/2$, where $r_0=\vert R_0\vert$. Thus

$$
U+\sum_{s\in R'_X}\operatorname{cost}(s)
 \ge\frac1{2+r_X+r_0}+\frac{r_0}2+\frac14+\frac34-\frac1{2(1+r_X)}.
$$

For $r_0=0$, this is at least $1+r_X/(2(1+r_X)(2+r_X))$. For $r_0\ge1$, it is at least $1/4+1/2+3/4-1/4$. $\square$

#### 7.9 Theorem S1'

**Theorem S1' (G3h' when $t_2(A)=1$ or $d_x=2$).** In setting S, G3h' holds with

$$
c(A)-\operatorname{act}(A)D>1/k_{uw}
$$

whenever (a) the groups $\mathcal B,\mathcal C$ of $A$ have no type-2 slot, so $t_2(A)=1$, with $R_x$ edges allowed; or (b) $d_x=2$, for any anchor.

*Proof.* Lemma S2 and the slack bound after Lemma S8 give

$$
c(A)-\operatorname{act}(A)D\ge\frac1{k_{uw}}+\frac{|\mathcal A_0|}2
     +\Lambda_u+\Lambda_w+s_u+s_w,
$$

where $\Lambda_u=U+S_1-2$ if $T_1$ is deficient, and $\Lambda_u=U-11/12$ otherwise; $\Lambda_w$ is its mirror. Let $\alpha$ indicate that the bicone of the unique type-2 slot of $\mathcal C$ is active. By Lemma S8, $\alpha\le[r_2=1]$. Then

$$
s_u=\frac{r_2-\alpha}{6}+\alpha(1/6-D)
 \ge\left[r_2=1\right]\left(1/6-D\right)+\frac{[r_2\ge2]}3.
$$

Also $1/6-D\ge S_1-1$ when $T_1$ is deficient, since $D\le\operatorname{def}(T_1)+1/12$ and $S_1-1=1/12-\operatorname{def}(T_1)$.

For (b), $d_x=2$. Lemma S10 gives

$$
\Lambda_u+s_u\ge U^-+S_1+\sigma_u-2>0,
$$

and likewise for $w$. The quantities $s_u,s_w$ come from different type-2 slots, so nothing is counted twice.

For (a), it remains to treat $t_2(A)=1$, $d_x=1$, and $T_1$ deficient; the case with $T_2$ deficient is its mirror. We have

$$
\begin{aligned}
 \Lambda_u+\Lambda_w
  &=(U^-+S_1-2)\\
  &\quad+\left(W+\sum_{s\in R_X\cup R_0}\operatorname{cost}(s)-11/12\right).
\end{aligned}
$$

The first bracket is positive by Lemma S10, with $\sigma_u=0$. The second is nonnegative by the mirror of the corollary of Section 7.4 if $A$ has no $R_x$ edge, and by the mirror of Lemma S11 otherwise. $\square$

**What remains after Theorem S1'.** Setting S has $d_x\in\{1,2\}$ by Lemma P. Theorem S1'(b) covers $d_x=2$, and Theorem S1'(a) covers $d_x=1$ with no type-2 slot in $\mathcal B\cup\mathcal C$. The remaining case, $d_x=1$ with a type-2 slot in $\mathcal B\cup\mathcal C$, is Theorem S3 of Section 8.

### 8. G3h' when $d_x=1$ and $\mathcal B\cup\mathcal C$ has a type-2 slot

**Theorem S3.** In setting S with $d_x=1$, if $\mathcal B\cup\mathcal C$ contains a type-2 slot, then

$$
c(A)-\operatorname{act}(A)D>\frac1{k_{uw}}.
$$

By the symmetry $u\leftrightarrow w$, assume that $T_1$ is deficient and $T_2$ is not. Thus
$D=\operatorname{def}(T_1)=13/12-S_1$, and $0<D\le1/12$, since Theorem 1 of subdivision 2 gives $S_1\ge1$.
The inputs are F1, Lemmas 1 and 2 and Theorem 1 of Section 2; Theorem G1; Lemmas S1, S2, S6, S8, S9, S10.1 and S10 of Section 7; and $U^-+S_1\ge\Psi_N-L^*$ from Section 7.7.

#### 8.1 Notation for both sides

Write

$$
\mathcal C=\{v\}\cup R,\qquad R=R_U\cup R_X\cup R_0\cup R_2,
 \qquad k=|R_U|,\ n_C=|R_X|,\ r_0=|R_0|,\ m=|R_2|.
$$

These four classes consist respectively of type-1 slots in $R_u$, type-1 slots in $R_x$, isolated slots, and type-2 slots. On the other side write

$$
\mathcal B=\{v\}\cup R'_W\cup R'_X\cup R'_0\cup R'_2
$$

with corresponding cardinalities $k',n_B,r'_0,m'$. Also

$$
\mathcal A=\{y\}\cup\mathcal A_u\cup\mathcal A_w\cup\mathcal A_0,
 \qquad J_2=(Q\cap M)\setminus\{x,y\}\subseteq\mathcal A_w,
 \qquad a=|\mathcal A_w|,\quad c=1+k'.
$$

By Lemma S1(d), $y$ is the only type-2 slot of $\mathcal A$.
If $m\ge1$, let $z^*$ be the common partner of $R_2$ from Lemma S8(a). Then

$$
z^*\in(M\cap X_w)\setminus\{x,u,v\},\qquad z^*\notin X_u,
 \qquad z^*\in\mathcal A_u.
$$

If $m'\ge1$, its mirror $z'^*$ satisfies

$$
z'^*\in(M\cap X_u)\setminus\{x,w,v\},\qquad z'^*\notin X_w,
 \qquad z'^*\in\mathcal A_w.
$$

Indeed, $z^*\in\mathcal A$ is $R_u$-adjacent to $R_2$ and cannot be $y$, whose only $R_u$-neighbour is $v$ by Lemma S1(b). Since every slot of $R_2$ has a unique $R_x$-neighbour by Lemma 2 of subdivision 2, every $R_x$-neighbour of a slot of $R'_X$ lies in $R_X$, except that $z^*$ may also be adjacent to $R_2$. Set

$$
U^-=U-\sum_{R_X\cup R_0}\operatorname{cost},\qquad
 W^-=W-\sum_{R'_X\cup R'_0}\operatorname{cost}.
$$

Let $\alpha_u$ indicate that the bicone of the unique type-2 slot of $\mathcal C$ is active; set $\alpha_u=0$ if $m\ne1$. Define $\alpha_w$ by symmetry. Then
$\operatorname{act}(A)=1+\alpha_u+\alpha_w$: the triangle options of $A$ are those of $y,R_2,R'_2$ by Lemma S1(e), distinct options give distinct bicones, $B_q$ is active, and Lemma S8(b) excludes active bicones of type-2 slots when their group has at least two slots.

**Identity (1).** With $t_2(A)=1+m+m'$, define

$$
\begin{aligned}
 G_u&=U^-+\frac{r_0}2+S_1-2,\\
 H_w&=W^-+\frac{r'_0}2-\frac{11}{12}+X,\\
 X&=\sum_{R_X}\operatorname{cost}+\sum_{R'_X}\operatorname{cost}
       +\frac{m+m'}6.
\end{aligned}
$$

Then

$$
c(A)-\operatorname{act}(A)D
 =\frac1{k_{uw}}+\frac{|\mathcal A_0|}2+G_u+H_w-(\alpha_u+\alpha_w)D.
 \tag{1}
$$

*Proof.* Lemma S2 gives

$$
c(A)=\frac1{k_{uw}}+\frac{1+m+m'}6+\frac{|\mathcal A_0|}2+U+W-2,
$$

where $U=U^-+\sum_{R_X}\operatorname{cost}+r_0/2$, and similarly for $W$.
Subtract $(1+\alpha_u+\alpha_w)(13/12-S_1)$ and use $1/6-13/12=-11/12$.
$\square$

#### 8.2 Where the partners sit

**Lemma N.** If $m\ge1$, then $z^*$, as a slot of $\mathcal B$, lies in $R'_X$.
By symmetry, if $m'\ge1$, then $z'^*$, as a slot of $\mathcal C$, lies in $R_X$.

*Proof.* The slot $z^*\in\mathcal B$ is $R_x$-adjacent to every slot of $R_2$, so is not isolated. Suppose it is type 2. Lemma 2 of subdivision 2 says its two neighbours are slots of one vertex, so $R_2=\{r\}$ and its $R_w$-neighbour is $r\in\mathcal A$, giving $wrz^*\in H$. The type-2 slot $r\in\mathcal C$ has partner $z^*$, so its $R_u$-neighbour is $z^*\in\mathcal A$, giving $urz^*\in H$. Hence $\{r,z^*\}\in\operatorname{CN}(u,w)$; the pair avoids $\{u,w\}$ because $r\in X_u\setminus\{w\}$ and $z^*\in X_w$.
But $xv\in\operatorname{CN}(u,w)$ since $T_1,T_2\in H$, and
$\{r,z^*\}\cap\{x,v\}=\varnothing$: neither vertex is $x$, as they belong to $L(xu),L(xw)$; $r\ne v$, since $v\in\mathcal C$ has no $R_x$ edge by Lemma S1(c); and $z^*\ne v$ by Lemma S8(a). These disjoint members of $\operatorname{CN}(u,w)$ contradict F1. Thus $z^*$ has $R_x$ edges and no $R_w$ edge, and is type 1 in $R_x$.
$\square$

Consequently the *mutual case*, meaning $m=m'=1$ with $z^*$ the type-2 slot of $\mathcal B$ whose partner is the type-2 slot of $\mathcal C$, cannot occur in an avoiding host. Lemma N has no exception.

#### 8.3 The $u$-side

**Lemma U.** If $T_1$ is deficient, then:

- **(a)**  $m=0$ implies $G_u>0$;

- **(b)**  $m=1$ implies $G_u>D-1/12$;

- **(c)**  $m\ge2$ implies $G_u>-m/(3(m+3))$.

*Proof.* We have $G_u\ge U^-+S_1-2$. Parts (a) and (b) follow from Lemma S10 with $\sigma_u=0$ and $\sigma_u=S_1-1=1/12-D$, respectively.
For (c), Section 7.7 gives $U^-+S_1\ge\Psi_N-L^*$, where

$$
L^*=\begin{cases}
 \dfrac1{2+k}-\dfrac1{2+k+m},&z^*\in J_1,\\[4pt]
 \dfrac1{2(1+k)}-\dfrac1{2(1+k+m)},&z^*\in E_u.
 \end{cases}
$$

Lemma S10.1, using Lemma S9, gives $\Psi_N>2$.
If $k\ge1$, both expressions decrease with $k$, so

$$
L^*\le\max\left\{\frac{m}{3(3+m)},\frac{m}{4(2+m)}\right\}
 =\frac{m}{3(m+3)},
$$

since $3(3+m)\le4(2+m)$ for $m\ge1$. Hence $G_u>-m/(3(m+3))$.

If $k=0$, then $k<j$, since Lemma S9 gives $j\ge2$. Thus case (ii) or (iii) of Lemma S10.1 applies. This uses its case bounds, not just the statement of Lemma S10. In case (ii), $\Psi_N-2\ge10/7>1/2>L^*$. In case (iii),

$$
\Psi_N\ge\chi(j+1)+(r-k)
 \left[\frac{j}{(2+k)(2+r)}-\frac1{2(1+j)}\right],
$$

where $\chi(j+1)>2$ and $j\ge r+1$. At $k=0$ the bracket is at least

$$
\frac{r+1}{2(r+2)}-\frac1{2(r+2)}=\frac r{2(r+2)}.
$$

Therefore $\Psi_N-2>r^2/(2(r+2))\ge m^2/(2(m+2))$, using $r\ge m$ and monotonicity. Also, at $k=0$,

$$
L^*\le\max\left\{\frac m{2(2+m)},\frac m{2(1+m)}\right\}
 =\frac m{2(m+1)}.
$$

The inequality $m^2/(2(m+2))\ge m/(2(m+1))$ is equivalent to $m^2\ge2$. Hence

$$
G_u>0\ge-\frac{m}{3(m+3)}.
$$

$\square$

#### 8.4 The $w$-side (Lemma W)

Put $N=n_B+m'$ and define, with brackets denoting indicators,

$$
\tau_W=\begin{cases}
 [m'=1]/12,&m=0,\\
 1/6,&m=1,\ m'=1,\\
 1/12,&m=1,\ m'\ne1,\\
 \dfrac{m}{3(m+3)}+[m'=1]/12,&m\ge2.
 \end{cases}
$$

**Lemma W.** $H_w\ge\tau_W$.

*Proof. Step 1: the $R_w$ part.*
The costs of slots in $\mathcal B\setminus(R'_X\cup R'_0\cup R'_2)$ and $\mathcal A_w$ are bounded by degree caps. Each cap contains all neighbours of the slot. The slot $v\in\mathcal B$ costs exactly $1/(2(2+\vert J_2\vert ))\ge1/(2(2+a))$ by the mirror of Lemma S1(c). A slot of $R'_W$ has its $R_w$-neighbours in $\mathcal A_w$, since $y$ is adjacent only to $v$, giving cap $a$. A slot of $J_2$ is adjacent to $v$ and slots of $R'_W$; a slot of $\mathcal A_w\setminus J_2$ only to $R'_W$, since it is not in $Q$; and $z'^*$ additionally to $R'_2$. These give caps $c$, $c-1$, and $c+m'$ for $z'^*$.
The expression $g_W$ below uses the weaker uniform cap $c$ for all slots of $\mathcal A_w$; the exceptional extra neighbours of $z'^*$ are accounted for by $L'^*$.
Also $1/\vert X_w\vert =1/(1+c+N+r'_0)$. Removing the $r'_0$ isolated slots raises this term by at most $r'_0/6$, since $1+c+N\ge2$, and saves $r'_0/2$. Hence

$$
\begin{aligned}
 W^-+\frac{r'_0}2&\ge B-L'^*,\\
 B&=\frac1{1+c+N}+g_W(a,c),\\
 g_W(a,c)&=\frac1{2(2+a)}+\frac{c-1}{2(1+a)}+\frac a{2(1+c)},
\end{aligned}
$$

where $L'^*=0$ for $m'=0$, and
$L'^*=1/(2(1+c))-1/(2(1+c+m'))$ for $m'\ge1$. In the latter case $a\ge1$, since $z'^*\in\mathcal A_w$.
We claim

$$
B-L'^*\ge\beta:=\begin{cases}
 \dfrac14+\dfrac1{2+N},&m'=0,\\[4pt]
 \dfrac16+\dfrac1{2+N}+\dfrac1{2(2+m')},&m'\ge1.
 \end{cases}
$$

For $c\ge2$, Lemma S6 gives
$g_W=f(a,c)-1/(1+c)\ge11/12-1/(1+c)$.
Since $1/(1+c+N)-1/(1+c)$ increases with $c$,

$$
B\ge\frac7{12}+\frac1{3+N}\ge\frac14+\frac1{2+N}.
$$

For $m'\ge1$, we have

$$
B-L'^*\ge\frac{11}{12}-\frac3{2(1+c)}
                 +\frac1{1+c+N}+\frac1{2(1+c+m')}.
$$

This expression increases with $c$, and at $c=2$ exceeds the claimed bound by

$$
\frac14-\frac1{(2+N)(3+N)}-\frac1{2(2+m')(3+m')}>0.
$$

For $c=1$, equivalently $k'=0$, the function
$g_W(a,1)=1/(2(2+a))+a/4\ge1/4$ increases with $a$.
Thus $B\ge1/4+1/(2+N)$ for every $N\ge0$. If $m'\ge1$, then $a\ge1$ and

$$
g_W(a,1)-L'^*=\frac1{2(2+a)}+\frac{a-1}4+\frac1{2(2+m')}
 \ge\frac16+\frac1{2(2+m')}.
$$

The argument does not infer $N\ge1$ merely from $\vert X_w\vert \ge3$: the identity
$\vert X_w\vert =2+N+r'_0$ would give only $N+r'_0\ge1$.
Nevertheless $N\ge1$ holds in Theorem S3's domain. If $m'\ge1$, then $N\ge m'$; otherwise $m\ge1$, so Lemma N gives $z^*\in R'_X$ and $n_B\ge1$.

*Step 2: the $R_x$ part.*
By Section 8.1 and Lemma N, if $m\ge1$, then $z^*\in R'_X$ has cap $n_C+m$, while every other slot of $R'_X$ has cap $n_C$. If $m'\ge1$, then $z'^*\in R_X$ has cap $n_B+m'$, and the others have cap $n_B$. A type-1 slot needs a neighbour, so $n_C=0$ forces $R'_X\subseteq\{z^*\}$, and $n_B=0$ forces $R_X\subseteq\{z'^*\}$. Therefore $H_w\ge\Theta'$, where

$$
\begin{aligned}
 \Theta'&=\beta+X_B+X_C+\frac{m+m'}6-\frac{11}{12},\\
 X_B&=\frac{[m\ge1]}{2(1+n_C+m)}
          +\frac{n_B-[m\ge1]}{2(1+n_C)},\\
 X_C&=\frac{[m'\ge1]}{2(1+n_B+m')}
          +\frac{n_C-[m'\ge1]}{2(1+n_B)}.
\end{aligned}
$$

*Step 3: reduction to a box.*
Directly from the definition, $\beta\ge1/6$, $\tau_W\le(m+m')/6$, and $\tau_W<5/12$; here $m/(3(m+3))<1/3$.
The stronger purported bound $\tau_W\le11/28$ is false from $m=40$ onward:
$\tau_W(40,1)-11/28=1/1806$. Only $\tau_W<5/12$ is used.

- **(i)**  If $m+m'\ge7$, then

$$
\Theta'-\tau_W\ge\frac16+\frac76-\frac{11}{12}-\frac5{12}=0.
$$

- **(ii)**  If $\min(n_B,n_C)\ge1$, then AM–GM gives

$$
\begin{aligned}
 X_B+X_C
 &\ge\frac{n_B-1}{2(1+n_C)}+\frac{n_C-1}{2(1+n_B)}\\
 &=\frac{n_B+1}{2(n_C+1)}+\frac{n_C+1}{2(n_B+1)}
      -\frac1{n_C+1}-\frac1{n_B+1}\\
 &\ge1-\frac1{n_C+1}-\frac1{n_B+1}.
\end{aligned}
$$

  This is at least $3/4$ if $\min(n_B,n_C)\ge7$. If instead
$1\le\min(n_B,n_C)\le6$ and $\max(n_B,n_C)\ge12$, the single term

$$
\frac{\max(n_B,n_C)-1}{2(1+\min(n_B,n_C))}\ge\frac{11}{14}\ge\frac34
$$

  suffices. In both cases
$\Theta'-\tau_W\ge1/6+3/4+(m+m')/6-11/12-\tau_W\ge0$.

- **(iii)**  If $\min(n_B,n_C)=0$, then $\max(n_B,n_C)\le1$ by Step 2.

It remains to check $\Theta'\ge\tau_W$ at the admissible integer points with
$0\le n_B,n_C\le11$ and $m+m'\le6$.

The admissible points $(n_B,n_C,m,m')$ are defined by:

- **(A1)**  $m+m'\ge1$, the hypothesis of Theorem S3;

- **(A2)**  $m\ge1\Rightarrow n_B\ge1$, and $m'\ge1\Rightarrow n_C\ge1$, by Lemma N and its mirror;

- **(A3)**  $n_C=0\Rightarrow n_B\le[m\ge1]$, and $n_B=0\Rightarrow n_C\le[m'\ge1]$, by Step 2.

Every configuration in Theorem S3's domain satisfies (A1)–(A3). These conditions imply $N\ge1$ and $n_C+m\ge1$, which the scripts also test. The scripts additionally evaluate the empty mutual variant at $m=m'=1$.

*Step 4: the finite check.*
The recorded exact certificate `wbox`, described in Section 10, reports
$\Theta'-\tau_W\ge0$ at all $3{,}279$ admissible points. Its minimum is zero, attained exactly at
$(n_B,n_C,m,m')=(1,0,1,0)$, corresponding to $\mathcal B=\{v,z^*\}$ and one type-2 slot in $\mathcal C$.
The alternative count $3{,}401$ includes $122$ points of the mutual variant, with another zero at $(0,0,1,1)$; that variant corresponds to no configuration by Lemma N.
$\square$

#### 8.5 Proof of Theorem S3

By (1),

$$
c(A)-\operatorname{act}(A)D-\frac1{k_{uw}}
 \ge G_u+H_w-(\alpha_u+\alpha_w)D.
$$

Use Lemmas U and W, $D\le1/12$, $\alpha_u\le[m=1]$ and $\alpha_w\le[m'=1]$.

-  If $m=0$, so $m'\ge1$, the right-hand side is strictly greater than
$\tau_W-[m'=1]D=\left[m'=1\right]\left(1/12-D\right)\ge0$.

-  If $m=1$, it is strictly greater than
$(D-1/12)+\tau_W-D-[m'=1]D$.
  This equals zero for $m'\ne1$, when $\tau_W=1/12$, and equals $1/12-D\ge0$ for $m'=1$, when $\tau_W=1/6$.

-  If $m\ge2$, then $\alpha_u=0$, and it is strictly greater than

$$
-\frac m{3(m+3)}+\tau_W-[m'=1]D=\left[m'=1\right]\left(1/12-D\right)\ge0.
$$

Lemma U supplies strictness in every case. Thus $c(A)-\operatorname{act}(A)D>1/k_{uw}$.
$\square$

### 9. Exhaustive case tree and conclusion

#### 9.1 The anchor condition in every case

In Setting S, $d_x\in\{1,2\}$ by Lemma P. Theorem S1'(b) of subdivision 7 covers $d_x=2$. If $d_x=1$ and $\mathcal B\cup\mathcal C$ has no type-2 slot, Theorem S1'(a) applies. If $d_x=1$ and it does have a type-2 slot, Theorem S3 of subdivision 8 applies. Hence in all cases

$$
c(A)-\operatorname{act}(A)D>\frac1{k_{uw}},\qquad \frac{c(A)}{\operatorname{act}(A)}>D,
$$

since $B_q$ is active, contains $A$, and therefore $\operatorname{act}(A)\geq1$. In particular G3h' holds.

#### 9.2 Coverage and dependency audit

The case tree for every triple $T$ is as follows.

-  If $c(T)\geq0$, Lemma D gives nonnegative final charge. Donors finish at zero; other such triples keep their charge and receive nothing.

-  If $T$ is deficient, G1 gives one triangle option and thus one active bicone, and makes $T$ exactly-one-light. Theorem 1 of subdivision 2 bounds its deficit by $1/12$.

-  At its apex $x$, Lemma P gives $1\leq d_x\leq2$ and a nondeficient anchor. A both-light anchor is covered by Lemma Q and supplies at least $1/6$ with activity one. A both-heavy anchor is covered by the three exhaustive branches of subdivision 9.1. In its one-deficient-triple branch with additional type-2 slots, the internal alternatives are $m=0$, $m=1$, and $m\geq2$. Lemma N excludes the mutual-partner configuration. The anchor group $\mathcal A$ has only the type-2 slot $y$, so

$$
t_2(A)=1+m+m',\qquad \operatorname{act}(A)=1+\alpha_u+\alpha_w,\qquad
 \alpha_u\leq[m=1],\quad\alpha_w\leq[m'=1].
$$

  The activity statements use Lemma S8, which uses G1 at every deficient triple of $H$, not only the two at the chosen apex.

-  Theorem C' adds the contributions of the distinct apex anchors. The resulting pot covers all deficits, and proportional redistribution gives $T$ at least its deficit.

Apexes with $d_x=0$ need no contribution. The dependencies are acyclic: subdivisions 7–8 use the slot results and G1; Theorem C' uses those conclusions and the both-light estimate, but none of them uses Theorem C'.

#### 9.3 Proof of the main theorem

Let $H$ be a finite avoiding $3$-graph. G1 holds at every deficient triple by subdivision 4, and G3h' holds for every relevant both-heavy anchor by subdivision 9.1. Theorem C' leaves every triple with nonnegative final charge. Conservation and the charge identity yield

$$
0\leq\sum_{T\in H}\operatorname{final}(T)
 =\sum_{T\in H}c(T)=|\partial H|+|\operatorname{CL}(H)|-2|H|.
$$

This is the main inequality. Each of $\partial H,\operatorname{CL}(H)$ lies in $\binom V2$, so $\vert H\vert \leq\binom{\vert V\vert }{2}$. The written deduction depends on the exact finite statements in subdivision 10 and on the local anchor estimates. Its exact conclusion is now Lean-verified; see the formal verification ledger.

### 10. Exact finite statements

Each statement below concerns finitely many rational numbers. The historical evidence consists of an exact primary implementation and an independent cross-check; for C1 with $t\leq1$, that cross-check uses rigorous directed rounding. An additional integer-only implementation now checks the four $t\leq1$ cases, with certified lower bound $8277463527/4294967296>23/12$. It was written after inspecting the primary implementation and shares its method, so it is not blind independent review. Six checks passed a fresh-virtual-environment replay on the same macOS arm64 machine with CPython 3.14.7 and NumPy 2.5.4. A source-level AI check matched the finite equations, domains, admissibility masks and integer pruning to the supplementary programs. Its scope does not include a new proof of the universal host-to-profile reductions. Floating-point exploration and finite-host stress tests are distinct from proof certificates.

**C1.**  For every $(t_A,t_B,t_C)\in\mathbb N^3$ with sum at most 11, and every

$$
(ab,ac,bc,ba,ca,cb)\in\{0,\ldots,92\}^6
$$

satisfying (F), $\Phi_{\rm prof}\geq23/12$. There are 364 triples of type-2 counts. No claim about the exact minimum or all minimisers is needed.

**C2.**  For every $(t_A,t_B,t_C)$ of sum at most 11 and every $(ab,ba,ca,cb)\in\{0,\ldots,92\}^4$ satisfying (F) for $R_a,R_b$,

$$
G+\kappa^*(ab+t_A,t_A)+\kappa^*(ba+t_B,t_B)\geq\frac{11}{12}.
$$

Here $\kappa^*(u,s)$ is the exact minimum of zero and $\kappa(p;u,s)$ over integers $23\leq p\leq160$, justified by the analytic tail argument. Equality occurs exactly at the two rest profiles

$$
\begin{array}{c|rrrr}
 (t_A,t_B,t_C)&ab&ba&ca&cb\\\hline
 (1,0,0)&0&0&0&1\\
 (0,1,0)&0&0&1&0
 \end{array}.
$$

**C1g(a).**  For every type-2 triple with $2\leq t\leq11$ and every feasible six-count profile in $\{0,\ldots,92\}^6$, $\Phi_{\rm prof}\geq2$. There are 360 type-2 triples in the domain, and exactly 41 equality profiles among 20 such triples.

**C1g(b).**  For $t=1$, each position of the type-2 slot and each of the four classes V1–V4 in subdivision 4.3, with partner constraints imposed, every feasible profile in $\{0,\ldots,92\}^6$ satisfies $\Phi_{\rm prof}\geq2$.

**C2g.**  Write $W=G+\kappa^*(ab+t_A,t_A)+\kappa^*(ba+t_B,t_B)$. For every type-2 triple with $2\leq t\leq11$ and every rest profile $(ab,ba,ca,cb)\in\{0,\ldots,92\}^4$ satisfying (F) for $R_a,R_b$, $W\geq1$, with exactly eight equality rest profiles. For $t=1$, the same lower bound holds on every noncompliant rest profile as defined in subdivision 4.3.

**Final anchor box.**  For every admissible $(n_B,n_C,m,m')$ satisfying (A1)–(A3) of subdivision 8.4, with

$$
0\leq n_B,n_C\leq11,\qquad 1\leq m+m'\leq6,
$$

one has $\Theta'(n_B,n_C,m,m')-\tau_W(m,m')\geq0$.
There are 3,279 admissible points. Equality occurs only at $(n_B,n_C,m,m')=(1,0,1,0)$. The impossible mutual variant is excluded from this domain.
The analytic inequalities and infinite-to-finite reductions have written proofs in the preceding subdivisions. Finite scans of those analytic inequalities and tests on hypergraph hosts corroborate those proofs but do not replace them. The exact programs, their implementation independence, commands, hashes and final replay results belong to the separate reproducibility record.

**Supplementary replay and equality records.**
The supplementary directory [computations](computations/README.md) contains code and a README. Its six-command runner is invoked as

```sh
<VENV_PATH>/bin/python -I <PACKAGE_PATH>/replay.py <RESULT_PATH>
```

with a result directory that does not already exist and a 240-second limit per check. The records [results/0-check_profiles.py.json](computations/results/0-check_profiles.py.json) and [results/1-check_profiles.py.json](computations/results/1-check_profiles.py.json) list respectively all 41 target-equality box vectors and the ten tail vectors (two at $11/12$, eight at $1$), including coordinate order, types, target and class context. Inclusive pruning retains equality candidates. These are target equalities, not a claim about auxiliary minima at other thresholds.

[results/semantic-hashes.json](computations/results/semantic-hashes.json) records normalized content hashes. Wall-clock run times may change raw output hashes; compare normalized mathematical content instead. The actual six-command receipt and eight runner controls are in [results/replay.json](computations/results/replay.json) and [results/runner-controls.json](computations/results/runner-controls.json). Independently coded rational controls check 5,832 profiles, 49,152 class masks, 1,248 tail parameter pairs, 5,000 rest profiles and all 3,279 corrected anchor points, with six cycle-pruning and nine tail-pruning cases. These bounded controls share dependencies and do not constitute independent full-domain reproduction, a universal host proof, or human review. The additional C1 integer-only implementation was written after inspecting the primary implementation and shares its method.

## Expanded structural and accounting arguments

The following arguments spell out the structural relabellings, exceptional-slot estimate, accounting identities and analytic reductions used in the proof. Finite tests corroborate particular substitutions but do not replace these universal arguments. The exact coefficient-one theorem has accepted complete Lean verification in the isolated proof project. This does not automatically verify every exposition below. The expanded supplementary source package passed its complete 126-module check. No human mathematical verification is claimed.

### A. Unrestricted avoidance and intersecting common links

This expands the common-link condition F1 in Section 2.1.
Suppose that $A,B,C,D$ are four distinct triples with

$$
A\cap B=C\cap D=\varnothing,\qquad A\cup B=C\cup D=S.
$$

Then $\vert S\vert =6$. The intersection $A\cap C$ has size one or two: size zero would force $C=B$, and size three would force $C=A$. Exchanging $C$ and $D$ if necessary, put $P=A\cap C$ with $\vert P\vert =2$. Write $A=P\cup\{x\}$ and $C=P\cup\{y\}$, where distinctness gives $x\ne y$. Put

$$
Q=S\setminus(P\cup\{x,y\}).
$$

Then $\vert Q\vert =2$, $B=Q\cup\{y\}$ and $D=Q\cup\{x\}$. Thus $P$ and $Q$ are disjoint members of $\operatorname{CN}(x,y)$. Together with F1, this proves that avoidance is equivalent to every common link being intersecting. No linearity assumption or additional forbidden configuration is used.

### B. The direction of the host-to-profile reduction

This clarifies Lemma 3 of Section 2.3. Only a one-way reduction is required: every actual triple of an avoiding host produces a feasible profile satisfying

$$
\sigma+\tau\ge\Phi_{\mathrm{prof}}.
$$

The numerical inequalities are proved over a possibly larger collection of feasible integer profiles. They do not assert that every profile is realizable by a host. Enlarging the domain is safe for a lower bound. A profile below a desired bound would need a separate realizability argument before it could be a hypergraph counterexample.

A vertex in two groups is counted as two slots. The associated options differ because each option meets $T$ in exactly one vertex, namely the vertex opposite its group. The partner identity for a type-2 slot follows from intersectingness of the common link, not from distinctness of all outside vertices. Cauchy–Schwarz bounds each type-1 class using its actual degrees; type-2 partners contribute at most one edge per slot. Removing isolated slots changes the sum by $\Delta_X\ge0$. Thus the reduction retains every actual host without assuming that the groups are disjoint.

### C. The six relabellings in Lemma S8(b)

This expands the application of Corollary 6g in Section 7.6.
Write $z=z^*$, fix $r\in R_2$, and assume $\vert R_2\vert \ge2$.
Every $s\in R_2$ lies outside $\{x,u,z,w\}$, and

$$
sxu,\quad suz,\quad sxz\in H.
$$

The already identified common links $\operatorname{CN}(w,s)$ are the full triangle $\{xu,uz,xz\}$. The three $w$-side triples have at least two triangle options, so G1(i) says that none is deficient. If an $r$-side triple is deficient, G1(ii) gives exactly one light pair incident with $r$. All possibilities are listed below. In each row apply Corollary 6g with

$$
a=r,\qquad b=p_1,\qquad c=p_2.
$$

The type-2 slot in the $a$-group is $w$, with partner $p_3$.

| Triple $T$ | Light pair | $p_1$ | $p_2$ | $p_3$ | Extra edge |
| --- | --- | --- | --- | --- | --- |
| $rxu$ | $rx$ | $x$ | $u$ | $z$ | $xzr'$ |
| $rxu$ | $ru$ | $u$ | $x$ | $z$ | $uzr'$ |
| $ruz$ | $ru$ | $u$ | $z$ | $x$ | $uxr'$ |
| $ruz$ | $rz$ | $z$ | $u$ | $x$ | $zxr'$ |
| $rxz$ | $rx$ | $x$ | $z$ | $u$ | $xur'$ |
| $rxz$ | $rz$ | $z$ | $x$ | $u$ | $zur'$ |

Here the extra edge exists for every $r'\in R_2\setminus\{r\}$.
For each row, the light pair $rp_1$ has precisely the neighbours $p_2,p_3$, so the $c$-group of $T$ is the singleton $\{p_3\}$. Corollary 6g says that the $b$-relation between this singleton and $L(p_1p_2)\setminus\{r\}$ consists of just the edge $p_3w$. But

$$
r'\in L(p_1p_2)\setminus\{r\},\qquad p_1p_3r'\in H
$$

by the three-triple property above. Also $r'\ne w,p_3$: we have $r'\in X_u\setminus\{v,w\}$, $z\notin X_u$, and a link vertex is neither $x$ nor $u$. Hence $p_3r'$ is a second edge in that relation, a contradiction. Every row is excluded, so the bicone of $\{w,r\}$ has no deficient member.

This argument requires G1 at every deficient triple of $H$, not merely at the original two triples $T_1,T_2$.

### D. Exceptional-slot accounting in Lemma S10

This expands the last $E_u$ subcase in Section 7.8.
Assume $r_2=1$, $z^*\in E_u$, and $j\ge r+1$. Then $e\ge1$, $r\ge k+1$, and the exceptional slot has degree at most $k+1$. The other $e-1$ slots of $E_u$ have degree at most $k$. Their contribution, together with the $k$ slots of $R_U$, is therefore at least

$$
E^*(e)=\frac{e-1}{2(1+k)}+\frac1{2(2+k)}
                      +\frac{k}{2(1+j+e)}.
$$

This equals the uncorrected term
$e/(2(1+k))+k/(2(1+j+e))$ minus exactly

$$
L^*=\frac1{2(1+k)}-\frac1{2(2+k)}.
$$

Thus $\Psi_N-L^*$ is obtained by replacing that $e$-term with $E^*(e)$; no other term changes. For real $e\ge1$,

$$
\frac{dE^*}{de}=\frac1{2(1+k)}-\frac{k}{2(1+j+e)^2}>0,
$$

since $j\ge r+1\ge k+2$. Consequently

$$
E^*(e)\ge E^*(1)=\frac1{2(2+k)}+\frac{k}{2(2+j)}
                     \ge\frac{k}{2(1+j)}.
$$

The left side minus the right side of the last inequality is

$$
\frac{(j+1)(j+2)-k(k+2)}{2(k+2)(j+1)(j+2)}\ge0.
$$

The $d$-terms, including $1/(P_d+1)$, remain minimized at $d=0$ by Lemma S5. Making that substitution gives a bound for the corrected expression itself:

$$
\Psi_N-L^*\ge\chi(j+1)+(r-k)
 \left[\frac{j}{(k+2)(r+2)}-\frac1{2(j+1)}\right]>2.
$$

Indeed $j\ge r+1$ and $k\le r$ give

$$
\frac{j}{(k+2)(r+2)}-\frac1{2(j+1)}
 \ge\frac{r+1}{(r+2)^2}-\frac1{2(r+2)}
 =\frac{r}{2(r+2)^2}\ge0.
$$

Also $\chi(j+1)>2$ by Lemma S10.1(iii).
Finally the local identity is $\sigma(T_1)+\tau(T_1)=11/12+S_1$. The $23/12$ bound therefore gives $S_1\ge1$, hence $\sigma_u=S_1-1\ge0$, so

$$
U^-+S_1+\sigma_u>2.
$$

The exceptional slot is charged once, inside $E^*$; $L^*$ must not be subtracted again.

### E. Global accounting without double-spending

This expands the accounting before the main theorem in Section 9.3.
Let $a(R)$ be the number of active bicones containing a positive-charge donor $R$. It spends $c(R)/a(R)$ on each of those $a(R)$ bicones, for total expenditure exactly $c(R)$. A bicone $q$ is active precisely when

$$
\delta_q=\sum_{T\in D_q}\operatorname{def}(T)>0,
$$

so proportional division is legitimate. It gives each $T\in D_q$ the amount

$$
\operatorname{pot}(q)\frac{\operatorname{def}(T)}{\delta_q}.
$$

Summing over $D_q$ returns exactly $\operatorname{pot}(q)$. G1 places each deficient triple in exactly one bicone, so paying one deficit does not require repeated receipts.

Within one bicone, if both apexes have positive deficit, their anchors are distinct triples: one contains $x$ and two base vertices, the other $y$ and two base vertices, and neither contains the other apex. An anchor may recur across bicones. Its anchor inequality uses the original share $c(R)/a(R)$ for the relevant bicone, not all of $c(R)$. Summing those shares over the active bicones never spends more than $c(R)$. A both-light anchor has $a(R)=1$; a both-heavy anchor uses the actual denominator, bounded by Lemma S8. Summing the anchor contributions over apexes with positive deficit within $q$ gives

$$
\operatorname{pot}(q)\ge\delta_q.
$$

Every receiver obtains at least its deficit, and all other triples finish nonnegative.

### F. Analytic tails and exhaustive partitions

This expands the finite-certificate reduction in Section 10. The profile certificate is not a search over hypergraphs.
If $t\ge12$, then $t/6\ge2$ already suffices. Otherwise $t\le11$. A non-big relation, with one count at most $22$ and another at least $93$, contributes

$$
S(93,22,11)=\frac{8649}{4300}>2
$$

by monotonicity. At least two big relations give

$$
2-\frac1{12}+t\left(\frac16-\frac1{576}\right),
$$

which is at least $23/12$ for $t\ge0$ and greater than $2$ for $t\ge1$. No big relation leaves all six counts in $[0,92]$. Exactly one big relation leaves four bounded counts and two unbounded ones, handled by $\kappa$.

Writing $x=p+1$, the sign of $\kappa$ is the sign of

$$
x^2-(u+s)x-su,
$$

since its denominator is $2x^2(x+u)>0$. Here $0\le u\le103$ and $0\le s\le11$. At $x=161$, its numerator is at least

$$
161^2-114\cdot161-1133=6434>0,
$$

and its derivative $2x-u-s$ is positive thereafter. Thus $p>160$ cannot lower $\min(0,\kappa)$; scanning $p=23,\ldots,160$ suffices. In fact $p=160$ already has positive numerator. This bounds every larger integer analytically, rather than sampling finitely many large values.

For G1 at $t=1$, the partner constraints force both neighbouring group sizes to be at least one. Failure of compliance means that either both are at least two, both equal one, or exactly one equals one and its corresponding outgoing type-1 count is positive. These are cases V1–V4; their overlap is harmless. The host proof partitions deficient triples by their unique bicone, then by the anchor's two colours. In the both-heavy case it splits into $d_x=2$ and $d_x=1$, and the latter splits by the presence of a type-2 slot in $\mathcal B\cup\mathcal C$. G1 uses no later anchor conclusion.

For Lemma W, let $m,m'\ge0$. The elementary inequalities

$$
\frac{m}{3(m+3)}\le\frac m6\quad(m\ge2),\qquad
 \frac{[m'=1]}{12}\le\frac{m'}6
$$

give $\tau_W\le(m+m')/6$; also $\tau_W<5/12$. If $m+m'\ge7$, then

$$
\Theta'\ge\frac16+\frac76-\frac{11}{12}=\frac5{12}
$$

suffices. For positive $n_B,n_C$, the ordinary-slot terms give at least

$$
1-\frac1{n_B+1}-\frac1{n_C+1},
$$

which is at least $3/4$ if both counts are at least seven. If the smaller is in $\{1,\ldots,6\}$ and the larger is at least twelve, one term alone is at least $11/14>3/4$. If one count is zero, actual degree constraints force the other to be at most one. Every remaining point therefore lies in the stated $12\times12$ box with $m+m'\le6$.

The admissibility conditions follow from actual neighbours. The excluded mutual variant represents no host. A separate direct checker records exactly $3{,}279$ remaining points, distinguished from the historical $3{,}401$-point calculation. Its source identity and replay evidence are supplied in the computational supplement; this appendix does not replace that evidence.

## Exact equality examples and a tight local branch

Let $B$ have three vertices and let $X$ be a disjoint set of $k\ge1$ vertices. Put $\operatorname{cone}_k=\{P\cup\{x\}:P\in\binom B2,x\in X\}$. Its common links are stars for base-base pairs, triangles for apex-apex pairs, and empty for mixed pairs, so it is avoiding. Direct counting gives

$$
|H|=3k,\quad |\partial H|=3+3k,\quad |\operatorname{CL}(H)|=3+\binom k2,
 \quad\Phi(H)=-\frac{(k-3)(k-4)}2.
$$

Each triple has one pair of codegree $k$, two of codegree two, two base-base options of common-link size $k$, and $k-1$ apex-apex options of size three. Hence

$$
\sigma=1+\frac1k,\quad\tau=\frac1k+\frac{k-1}{6},\quad
 c=-1+\frac2k+\frac{k-1}{6}.
$$

For $k=3,4$, every charge and $\Phi$ are zero. These equality examples are not unions of $K_5$ blocks. Equality in the shadow–co-link bound does not assert equality in the weaker edge bound.

More generally, join two triples when they share a pair and call the connected components pair-components. Different components have disjoint shadows. A co-link pair $xy$ also belongs to only one component: each witness pair $P$ joins $xP$ to $yP$, and two witness pairs intersect by avoidance, joining their $x$-triples through a shared pair. Thus edges, shadow pairs and co-link pairs partition over pair-components, and $\Phi$ is additive over them. This observation supplies combinations of tight components without asserting an exhaustive classification.

**An explicit deficient host attaining Lemma W.**
Take seven singleton vertices $a,b,c,w,t,r,z$ and four disjoint sets $X,Z,E,Y$ of sizes $9,26,19,17$, all mutually disjoint. A pattern such as $bXZ$ denotes every triple with one vertex from each indicated class. Take exactly

$$
\begin{gathered}
abc,acw,abt,atw,btw,bcw,bcr,brz,crz,cwz,bwz,abz,\\
abX,bXw,bcZ,bXZ,abE,bEr,bEZ,bzZ,bwY,bYZ.
\end{gathered}
$$

This gives 1,307 triples on 78 vertices. Exact checks by common links and by disjoint-pair union collisions verify avoidance. For the bicone with apexes $c,t$ and base $a,b,w$, set $x=c,y=t,u=b,v=a$. The anchor is $A=bcw$, with

$$
c(abc)=-\frac{409}{755160},\quad c(acw)=\frac12,\quad
c(A)=\frac{367}{1566},\quad\operatorname{act}(A)=2.
$$

The active bicones containing $A$ have apex pairs $\{c,t\}$ and $\{w,r\}$. The slot groups are

$$
\mathcal A=\{t,z\}\cup X\cup Y,\quad\mathcal B=\{a,z\},\quad
\mathcal C=\{a,r\}\cup Z.
$$

In $\mathcal B$, with degree coordinates ordered as $(R_w,R_x)$, $a$ has relation degrees $(1,0)$ and $z$ has degrees $(0,1)$; $r$ is the unique type-2 slot of $\mathcal C$. Thus

$$
(n_B,n_C,m,m')=(1,0,1,0),\quad W^-=\frac7{12},\quad
X_{\rm cost}=\frac5{12},\quad H_w=\frac1{12}=\tau_W.
$$

Here $X_{\rm cost}$ is the cost sum called $X$ in subdivision 8.1, not the vertex class. The local Lemma W bound has no slack. Nevertheless, with $D=409/755160$ and $k_{uw}=29$,

$$
\frac{c(A)}{\operatorname{act}(A)}-D=\frac{792709}{6796440}>0,\qquad
c(A)-\operatorname{act}(A)D-\frac1{k_{uw}}=\frac{675529}{3398220}>0.
$$

This realizes the local equality coordinate with deficiency, not global equality or a proof of the universal anchor lemma. No limiting-rate assertion is inferred from this finite host.

The [explicit examples package](examples/README.md) supplies complete edge lists for [DA2](examples/hosts/da2-host.json), [cone_3](examples/hosts/cone3-host.json) and [cone_4](examples/hosts/cone4-host.json), a [standalone checker](examples/check_examples.py), and [exact results](examples/results.json). These finite checks do not prove the universal statements.

## Exact formal declaration inventory

The [source manifest](formal-evidence/source-manifest.json) and [source transformation record](formal-evidence/source-transformations.json) distinguish the retained receipt-source hashes from the exported source hashes. Some exported files omit introductory development comments; historical passing receipts refer to their recorded original source bytes. The ledger records export checks separately from those historical receipts. Supporting-bound receipts do not certify the coefficient-one theorem.

This inventory lists historical official passing receipts, reused after source-hash matching. It is not a new kernel run or verification of the coefficient-one theorem. The accepted coefficient-one and classical design-existence declaration inventories are described in the formal verification ledger; these older entries retain only their original historical receipt scope. Each full declaration name below is keyed to its receipt and source hashes in the supplementary [formal receipt ledger](formal-evidence/receipt-ledger.json). This table covers the subset of 48 M1–M5 declarations and the separately listed $9/8$ bound; the supplementary ledger also contains later bridge and exact-export checks. Arithmetic declarations named G1 or G3 must not be mistaken for the complete host-structural or anchor theorems.

| Exact declaration |
| --- |
| `Erdos643R3.G1Arith.G1` |
| `Erdos643R3.G1Arith.G3` |
| `Erdos643R3.G1Arith.lemma2g_profile` |
| `Erdos643R3.G1Arith.lemma3g` |
| `Erdos643R3.G3hpArith.lemma5` |
| `Erdos643R3.G3hpArith.lemma6` |
| `Erdos643R3.G3hpArith.lemma6_eq` |
| `Erdos643R3.G3hpArith.lemma9_arith` |
| `Erdos643R3.Lemma1g.CN_type2` |
| `Erdos643R3.Lemma1g.card_triangle_options` |
| `Erdos643R3.Lemma1g.light_ab_iff` |
| `Erdos643R3.Lemma1g.light_ac_iff` |
| `Erdos643R3.Lemma1g.triangular_iff_type2` |
| `Erdos643R3.Lemma3.lemma3` |
| `Erdos643R3.Lemma3.lemma3_plus` |
| `Erdos643R3.Pw2312.Feas_rot` |
| `Erdos643R3.Pw2312.Phi_le_PhiPlus` |
| `Erdos643R3.Pw2312.Phi_named` |
| `Erdos643R3.Pw2312.Phi_rot` |
| `Erdos643R3.Pw2312Main.card_le_O` |
| `Erdos643R3.Pw2312Main.card_le_choose` |
| `Erdos643R3.Pw2312Main.card_le_shadow_colink` |
| `Erdos643R3.Pw2312Main.per_triple` |
| `Erdos643R3.Pw2312Main.theorem2` |
| `Erdos643R3.Pw2312.E1` |
| `Erdos643R3.Pw2312.E3` |
| `Erdos643R3.Pw2312.E4` |
| `Erdos643R3.Pw2312.K_ge` |
| `Erdos643R3.Pw2312.S_one_sided` |
| `Erdos643R3.Pw2312.caseI_rel01` |
| `Erdos643R3.Pw2312.kappa_nonneg` |
| `Erdos643R3.PwC1.c1_cert` |
| `Erdos643R3.PwC1.caseII` |
| `Erdos643R3.PwC2.c2_cert` |
| `Erdos643R3.PwC2.caseIII` |
| `Erdos643R3.PwCheck.bb2_sound` |
| `Erdos643R3.PwCheck.bb_sound` |
| `Erdos643R3.PwCheck.kdC_sound` |
| `Erdos643R3.RedistArith.F_eq_zero` |
| `Erdos643R3.RedistArith.F_nonneg` |
| `Erdos643R3.RedistArith.lemma_P` |
| `Erdos643R3.SlotModel.card_CN_slot` |
| `Erdos643R3.SlotModel.group_exact` |
| `Erdos643R3.SlotModel.lemma2` |
| `Erdos643R3.SlotModel.sigmaW_slots` |
| `Erdos643R3.SlotModel.tauW_slots` |
| `Erdos643R3.WBox.wbox` |
| `Erdos643R3.WBox.wcheck_true` |
| `Erdos643R3.WeightingBound.card_le_nine_eighths_choose` |

The table below identifies the historical original source closure imported by the $23/12$ module. These are receipt-source hashes, not hashes of transformed export files; the supplementary ledger tracks that distinction. In particular, `WeightingAuxArith` is included as a dependency; this listing does not manufacture a separate declaration-level receipt for it.

| Module | SHA-256 |
| --- | --- |
| `HypergraphBasics` | `bb5c59fb53d56a61a18fe3b844631267495e11567d6e4096586161adc3f6f78b` |
| `Identity` | `bb8e2c89c58a5603e0c938ff5f116c8210f85d1df310100a9c3c91f337b8ef8b` |
| `Lemma3` | `da25f9bfd995303e19960a2a03e0e7da1bd66462cfa53aa1e45a266aa015b3e2` |
| `Pw2312` | `9f50b40348bc328e104c73f03fc372ee34424d222f19f0ce21004f7510accb6e` |
| `Pw2312Defs` | `13db77e821077d1d3eca6ab97c9e5fed68a92c9240c37932670e879287f1db09` |
| `PwArith` | `775743d33a23de323700c2a45c27dd107e03f3c9f1df09fb67f2bd40a688e647` |
| `PwC1` | `c2e7239a8562b3819a2fee8e4cf6fb8ffaa3045ff6758d10679ca042d4eefc40` |
| `PwC2` | `5276c63d7e3d39544c2e9358e55b847c34b8677b766fdb7131242f1cceda942b` |
| `PwCheck` | `29eedd06ab7523615d35a018322e4c7d40ac23c5b545ccff28c0415797dd6a88` |
| `SlotModel` | `224fd2eff3cce476bdad55c1ad3835cdeb7c0808175ecded175203ce7c0c3cee` |
| `Weighting` | `2d0688fdac329d0bb446d54c8fa665856949c7360350dc451ca6d4afe005348a` |
| `WeightingAuxArith` | `f598c850547c73b671bdb0c3f13546d21374d7d652630e1eb489a82c59580442` |
| `WeightingBound` | `ceb807e36820a80b6eb67e4199f7968306946a35f0a7b85a92230660c08a55c6` |

## Review and formalization boundary

The six relabellings and exceptional-slot calculation are written out in Appendix [Expanded structural and accounting arguments](#expanded-structural-and-accounting-arguments); they are mathematical parts of the argument, not appeals to unavailable review notes. AI systems checked parts of the argument, with conclusions conditional on the stated mathematical inputs. These written checks do not constitute human review. The separate accepted Lean verification covers the exact final declarations and their complete checked dependency closure.

**Verification and review.** The ten exact final exports have complete official Lean verification and independent exact-source acceptance in the isolated proof project: nine are unconditional and one assumes a supplied block design. All 65 modules in their dependency closure were built, scanned and independently kernel-replayed. The expanded transformed supplementary source package passed its complete 126-module check, including the classical general design construction and exact admissible-order extremal and forcing values. Formal coverage applies to the exact declarations and their checked dependencies, not automatically to every written argument in this manuscript. General five-block design existence is covered through the separate exact construction declaration; the original Hanani papers were visually read, without independently revalidating every finite table or block entry or formally auditing the historical proofs. No human verification of any mathematical step is claimed. Robert Huynh directed the research and preparation of this manuscript.

## References

### Reference 1

Z. Füredi,
Hypergraphs in which all disjoint pairs have distinct unions,
*Combinatorica* **4** (1984), 161–168.
[Source](https://doi.org/10.1007/BF02579216).

### Reference 2

P. Frankl and Z. Füredi,
A new extremal property of Steiner triple-systems,
*Discrete Mathematics* **48** (1984), 205–212.

### Reference 3

O. Pikhurko and J. Verstraëte,
The maximum size of hypergraphs without generalized 4-cycles,
*Journal of Combinatorial Theory, Series A*
**116** (2009), 637–649.
[Source](https://doi.org/10.1016/j.jcta.2008.09.002).

### Reference 4

D. Mubayi,
Some exact results and new asymptotics for hypergraph Turán numbers,
*Combinatorics, Probability and Computing*
**11** (2002), 299–309.
[Source](https://doi.org/10.1017/S0963548301005028).
The restricted bound is journal Theorem 1.3; the author manuscript dated
11 June 2005 numbers it Theorem 1.4.

### Reference 5

Hao Huang, Jie Ma and Tianchi Yang,
Extremal hypergraphs without generalized 4-cycles,
arXiv:2609.37744v1 (29 September 2026).
[Source](https://arxiv.org/abs/2609.37744v1).

### Reference 6

L. Howard,
*Disjoint Union-Free 3-Uniform Hypergraphs*,
M.Sc. thesis, University of Victoria, 2006.
[Source](https://hdl.handle.net/1828/1868).

### Reference 7

P. J. Dukes and A. C. H. Ling,
Disjoint union-free designs with block size three,
*Bulletin of the Institute of Combinatorics and its Applications*
**45** (2005), 5–10.

### Reference 8

Erdős Problems, Problem 643,
[Source](https://www.erdosproblems.com/643), accessed 19 October 2026.

### Reference 9

P. Erdős, Problems and results in combinatorial analysis,
*Congressus Numerantium* **19** (1977), 3–12.
[Source](https://users.renyi.hu/~p_erdos/1977-24.pdf).

### Reference 10

H. Hanani, The existence and construction of balanced incomplete block designs,
*Annals of Mathematical Statistics* **32** (1961), 361–386.
[Source](https://doi.org/10.1214/aoms/1177705047).
The five-block result is (7.10), pp. 378–380, with the 141-point exception completed by the 1965 note.

### Reference 11

H. Hanani, A balanced incomplete block design,
*Annals of Mathematical Statistics* **36** (1965), 711.
[Source](https://doi.org/10.1214/aoms/1177700182).
This note supplies the 141-point case and removes the exceptions in the 1961 statement (7.10).
