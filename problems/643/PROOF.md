# Exact four-thirds bound

This written argument uses the explicitly attributed PV lemmas below. The formal package also proves those suppliers. HMY motivated the pair-charge approach; its r≥4 theorem is not assumed here. See [SOURCES.md](SOURCES.md) and [VERIFICATION.md](VERIFICATION.md).

## Statement and definitions
For every nonnegative integer n, every simple 3-uniform hypergraph F on n vertices avoiding four DISTINCT edges A,B,C,D with A∪B=C∪D and A∩B=C∩D=∅ has

|F|≤(4/3)binom(n,2).

Thus ex_3(n)≤floor((4/3)binom(n,2)), and the forcing threshold is at most floor((4/3)binom(n,2))+1. This is a coefficient improvement of 1/9 over PV’s 13/9; no claim of the conjectured coefficient 1.

For a graph L, D(L) denotes its pairs with at least two common neighbors, and E(L) pairs with exactly one. Write e(L) for its edge set; E(L) is reserved for these half-diagonal pairs. For any 3-graph G, D(G) is the union of D(L_G(v)) over all vertex links, and E(G) is the union of E(L_G(v)) minus D(G). Write B(G)=D(G)∪E(G). All pairs are unordered sets of distinct vertices.

CN_G(x,y)=L_G(x)∩L_G(y), a graph of pairs disjoint from x,y. A star includes an empty family or any pair family with a common vertex.

PV is Pikhurko–Verstraëte, The Maximum Size of Hypergraphs without Generalized 4-Cycles, JCTA 116 (2009), author PDF dated 30 December 2007, available from the [author’s public manuscript](https://mathweb.ucsd.edu/~jverstra/generalizedc4.pdf).

We use exactly three external lemmas:
- PV Lemma 3: every graph L has R⊆e(L), |R|≤|D(L)|, such that each original diagonal of L has zero common neighbors in L\R. This kills half-diagonal remnants as well as diagonals.
- PV Lemma 7: let G be forbidden-free. Suppose distinct root triples T,T' have kernel sets P,P' with P disjoint from T, P' disjoint from T', and |P|,|P'|≥2. Suppose G contains every triple formed from a root pair and one corresponding kernel vertex. If the pair families binom(T,2)∪binom(P,2) and binom(T',2)∪binom(P',2) intersect, then G contains a member of K5−. K5− is PV's three-type family with≥8 triples and any two missing triples meeting in exactly one vertex.
- PV Lemma 11: every forbidden-free F admits R⊆F such that G=F\R is K5−free and |B(G)|≤binom(n,2)−|R|.

## 1. Faithful characterization
Forbidden-free G is equivalent to every CN_G(x,y) being intersecting. Two disjoint pairs P,Q in CN_G(x,y) give xP,yQ,xQ,yP, four distinct triples on precisely six vertices. Conversely the crossing intersection matrix of two distinct partitions of a six-set into two triples has entries 1,2,2,1 after reordering. Its singleton cells give x,y and its two-element cells give P,Q.
Every intersecting graph is a star or exactly a triangle: if ab,ac exist and there is no common center a, an edge avoiding a must be bc; no fourth distinct pair meets ab,ac,bc simultaneously.

## 2. Abstract zero-compatibility deletion
Let H be a bipartite 3-graph on disjoint X,Y, every edge having one X and two Y vertices. Assume:
(i) Every CN_H(x,x') for distinct x,x'∈X is a star graph on Y.
(ii) For every distinct u,v∈Y for which CN_H(u,v) is nonempty, there exists w∈Y such that for every y∈Y\{u,v,w}, at most one x∈X satisfies xuy,xvy∈H.
Then there is Q⊆H with

|Q|≤|D(H)∪E_X(H)|,

such that every Y-pair has at most one X-neighbor in H\Q. E_X consists of those half-diagonal pairs lying in X. This is the empty-compatibility, no-triangle specialization suggested by HMY Section 6, proved here from PV Lemma 3.

Proof. Set P=D(H)∪E_X(H). All pairs in P lie entirely within X or entirely within Y: a link at X is on Y, and a link at Y is bipartite, so mixed pairs have no common neighbors.
Assign each X-pair in P to one vertex g(p)∈Y as follows. Its common-link graph CN_H(x,x') is nonempty and a star by (i). If it has at least two edges, assign its unique center. If it has one edge ab, assign either endpoint, say the smaller in a fixed order. (A nonempty star with at least two edges has a unique center.) Assign each Y-pair in D_Y(H) to a vertex w supplied by(ii). Such a vertex exists because the diagonal entails nonempty CN_H(u,v).
Write P_y={p∈P:g(p)=y}; these partition P.

Process Y in any fixed order, using only deletions. At the step y, let L be the current y-link, a bipartite graph on X and Y\{y}. Every diagonal of L belongs to P_y. For an X-pair, two neighbors in L mean two distinct original common Y-edges through y. By (i) those edges form part of a star; having two through y forces y to be its unique center, so g(p)=y. For a Y-pair uv, a diagonal in L gives at least two X-vertices satisfying xuy,xvy in the original H; since y≠u,v, (ii) forces y=g(uv). Thus D(L)⊆P_y.

Apply PV Lemma 3 to L. Delete the corresponding hyperedges, at cost≤|D(L)|, making every pair of D(L) have zero codegree in the resulting link. Now process each X-pair p∈P_y\D(L) that still has a common neighbor in this link, deleting one of its two incident graph edges. Such a pair had initial codegree at most one in L, and deletion cannot increase it. Thus one edge suffices. The extra cost is at most |(P_y\D(L))∩binom(X,2)|≤|P_y\D(L)|. Total cost at this step is≤|P_y|.
After this step every X-pair assigned to y has zero codegree in the y-link. All of its original common Y-edges contained y by construction of g, so it has no common Y-edge anywhere in the current hypergraph. Later deletions preserve this fact.
At the end every X-pair that ever had a common Y-edge has none: it lay in D_X(H)∪E_X(H)⊆P and was processed at its owner. Thus no two X vertices share a Y-pair, the desired conclusion. Summing step costs gives |Q|≤sum_y|P_y|=|P|. QED.

## 3. Exact all-star pair-charge inequality
Suppose every CN_J(x,z) is a star. Form disjoint copies X=V^X,Y=V^Y and H={x^X u^Y v^Y:x,u,v distinct, xuv∈J}. Then |H|=3|J|.
Assumption (i) of Section 2 is immediate. For (ii), a nonempty CN_H(u^Y,v^Y) consists of mixed pairs x^X y^Y encoding xy∈CN_J(u,v). Choose a center w of that nonempty original star. For y outside{u,v,w}, any x with xyu,xyv∈J must satisfy x=w, proving the required at-most-one condition.

We have the identity

|D(H)∪E_X(H)|=2|D(J)|+|E(J)|. (1)

Indeed X-diagonals correspond exactly to J-diagonals: two common neighbors in the y^Y-link encode the same four triples as two common neighbors in L_J(y). Y-diagonals in either an X-link or Y-link likewise encode precisely a diagonal in L_J(y), so D_Y(H) is a second copy of D(J). X-half-diagonals are the pairs having any common neighbor in some original link but no original diagonal, exactly E(J). Mixed pairs contribute nothing. This proves (1).
Apply Section 2 and bound remaining hyperedges by N=binom(n,2), one per Y-pair. Therefore

3|J|≤N+2|D(J)|+|E(J)|=N+|D(J)|+|B(J)|. (2)

No asymptotic error occurs.

## 4. Removing all triangular common links in a K5−free host
Suppose G is forbidden-free and K5−free. For each triple T define its full kernel

P_T={a∈V\T: aS∈G for every S∈binom(T,2)}.

Consider precisely those T with i_T=|P_T|≥2. PV Lemma 7 implies the private families binom(T,2)∪binom(P_T,2) are disjoint for distinct T. Each private pair lies in D(G): a kernel pair has two distinct root neighbors in the link of the third root; a root pair has two distinct kernel neighbors in the link of the third root. Consequently

sum_T[3+binom(i_T,2)]≤d:=|D(G)|. (3)

Choose one root pair S_T and one distinguished kernel a_T for each T. Delete Z=union_T{aS_T:a∈P_T\{a_T}}. Then

|Z|≤sum_T(i_T−1)≤(1/3)sum_T[3+binom(i_T,2)]≤d/3, (4)

because 3(i−1)≤3+binom(i,2) for every integer i≥2; the difference is(i−3)(i−4)/2≥0.
Let J=G\Z. If CN_J(x,y) were not a star, Section 1 says it would be a triangle on roots T. Then x,y∈P_T in original G and at least one differs from a_T; its triple on S_T was deleted. Contradiction. Thus every common link in J is a star. All kernels and charges refer to original G, so simultaneous deletion introduces no assumption about evolving centers.

## 5. Final all-host bound
Take R,G from PV Lemma 11; write q=|R|, d=|D(G)|, N=binom(n,2). Then

|B(G)|≤N−q, and q+d≤N. (5)

Take Z,J from Section 4. Deleting triples preserves the containments D(J)⊆D(G) and B(J)⊆B(G). Note E(J) need not be a subset of E(G); that false monotonicity is not used.
By (2) and (5),

3|J|≤N+d+(N−q)=2N+d−q.

Therefore

|F|=q+|Z|+|J|
≤q+d/3+(2N+d−q)/3
=2N/3+2(q+d)/3
≤4N/3.

QED relative to the three stated public PV lemmas.

