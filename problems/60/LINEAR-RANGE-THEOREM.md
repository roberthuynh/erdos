> AI-written exposition. The main result has [Lean verification](VERIFICATION.md); this does not certify every written intermediate statement. No human mathematical review is claimed.

# Linear-range exact C4 supersaturation and first-excess structure

## 1. Exact statement

Put c=10^-8. For every even integer q≥10^16 and every integer 1≤t≤cq, put

N=q²+q+1,    M=q(q+1)²/2.

Every simple graph G on N vertices with M+t edges contains at least t(q−1) ordinary unlabelled copies of C4.

Equality holds if and only if G is obtained from an orthogonal polarity graph of a projective plane of order q by adding a matching of t edges between its absolute vertices (its degree-q vertices).

For q a power of two, the known equality ex(N,C4)=M and the existing orthogonal polarity construction therefore give

h(N,t)=t(q−1)    for 1≤t≤10^-8 q.

The first statement is M-based for arbitrary even q. It does not identify M with ex(N,C4) when q is not a prime power, and does not assert existence of a projective plane at every even order. The equality classification includes the possibility that no equality host exists at a given order.

## 2. Written proof dependencies

The argument uses the following complete exported chain:

1. [Localization argument](LOCALIZATION-ARGUMENT.md), elementary §§1–7 through actual support.
2. [Linear-support theorem](LINEAR-SUPPORT-THEOREM.md), statement and full linear parameter audit.
3. [Core construction and retained paths](CORE-AND-RETAINED-PATHS.md), §§1–3.
4. [Count-based completion](COUNT-BASED-COMPLETION.md), contract and §§1–8, using the corrected cell-index transport argument in §3.
5. [Published source interfaces](SOURCES.md).

The aggregate selection lemma is proved within the localization argument, so no separate unprinted selection premise is imported. The square-root cover-cost and edge-density stability argument are not dependencies.

## 3. External inputs

See [Sources](SOURCES.md) for the published inputs used by this written argument and the separate formal proof. The Lean proof establishes the geometry specialization needed for the stated range and derives the powers-of-two extremal interpretation internally; it does not assume the external inputs as unproved axioms.

## 4. The first-excess producer on one actual host

The dependency chain proves the following interface. For even q≥10^16, real 1≤T≤cq, and a graph G_0 with M+1 edges and Z(G_0)<Tq, there is a polarity graph Q on the same vertex set such that

j_0=|E(G_0)\E(Q)|<2T.                                    (1)

Here is the assembly with the relevant supports retained. Linear localization gives S_0 of size at most 252T whose induced edges hit every C4, and gives total degree surplus above q+1 at most 20T. Select at most 20T actual degree-cap edges and add both endpoints to S_0, obtaining S_1 of size m≤292T. Set

F=G_0−E(G_0[S_1]).

This one graph is C4-free, has maximum degree at most q+1 and minimum degree at least q−318T. It has at most q−1+312T deficient vertices and at most 292T deeply deficient vertices. All original deep vertices were in S_0, and no outside-core degree changes. These satisfy the count-based completion theorem's bounds .999q, 1.001q and .001q respectively. Therefore F⊆Q for one polarity graph Q.

All edges in E(G_0)\E(Q) have both endpoints in S_1. An outside-core missing Q-edge must be incident to an outside vertex upgraded from original degree q to Q-degree q+1. Since Q has at least q+1 absolute vertices, counting the original deficient vertices bounds the number of missing Q-edges with an outside endpoint by m+20T.

For each actual added edge ab, at least q−1 pairwise edge-disjoint Q-three-paths are available. At most 2m have an internal vertex in S_1, and at most m+20T further paths are destroyed by a missing edge with an outside endpoint. Hence

Z(G_0)≥j_0(q−1−3m−20T)≥j_0(q−1−896T).

Since q−1−896T>q/2, (1) follows. This counts distinct one-added-edge cycles; deleting the actual j_0 added edges makes the entire host a subgraph of Q and therefore covers every original cycle, including those with several added edges.

## 5. Transfer to arbitrary surplus in the claimed range

Let G have M+t edges. It suffices to handle Z(G)≤t(q−1), covering both a putative strict counterexample and equality. Choose any spanning subgraph G_0 with M+1 edges. With T=t,

Z(G_0)≤Z(G)≤t(q−1)<tq.

Apply Section 4 to obtain Q with j_0<2t. Now consider the original G on the same vertex set, and write

j=|E(G)\E(Q)|,    δ=M−e(Q),    d=|E(Q)\E(G)|.

There are only t−1 edges of G outside G_0, so

j≤j_0+t−1<3t≤3cq<q/4.                                    (2)

No minimum-cover argument or stability theorem is needed. Exact edge balance gives

d=j−t−δ≥0,    δ≥0,    j≥t.

For each of the j actual non-Q edges, at least q−1 edge-disjoint Q-three-paths are available; at most d are destroyed by missing Q-edges. Every retained path gives an actual C4 in G with exactly that one non-Q edge. Such cycles for different non-Q edges are distinct. Therefore

Z(G)≥j(q−1−d)=j(q−1−j+t+δ),

Z(G)−t(q−1)≥(j−t)(q−1−j)+jδ≥0.                            (3)

The last factors are nonnegative by (2), q≥10^16, and j≥t≥1. This proves the lower bound. Cycles with multiple non-Q edges cannot weaken (3), and they are not excluded from the theorem's count.

## 6. Equality, including multiple-added-edge controls

If Z(G)=t(q−1), the strict positivity q−1−j>0 in (3) forces j=t and δ=0. Then d=0. Thus Q is orthogonal, Q⊆G, and exactly t edges have been added.

Every added edge must have exactly q−1 Q-three-paths; otherwise the disjoint one-added-edge cycle families already exceed the prescribed total. The source equality clause forces both endpoints of every added edge to be absolute.

Suppose ab and ac are two added edges sharing an endpoint. The nucleus w gives the additional actual cycle b-a-c-w-b. Its vertices are distinct because w is nonabsolute and a,b,c are distinct absolute vertices. It has two added edges, so it differs from every previously counted one-added-edge cycle. This contradicts equality. The added edges therefore form a matching.

Conversely, start with an even-order orthogonal polarity and add a matching of t edges on its absolute set. Each added edge creates exactly q−1 one-added-edge cycles. A C4 cannot contain adjacent matching edges. If it contained two opposite added edges, all four vertices would be absolute and its remaining two edges would join absolute vertices in Q, impossible by independence. Thus every cycle has exactly one added edge and the total is t(q−1). There are q+1 absolute vertices, so the stated t range fits within an available matching. At powers of two such a polarity exists, giving the sharp h(N,t) assertion.

## 7. Separate structural first-excess conclusion

For even q≥10^16, real 1≤T≤cq, and e(G)=M+1 with Z(G)<Tq, Section 4 gives one polarity Q with

j=|G\Q|≤Z(G)/(q−1−896T)<2T,
δ=M−e(Q)≥0,
d=|Q\G|=j−1−δ≥0.                                         (4)

In particular, all hosts satisfying Z(G)<cq² admit this conclusion with T=cq. They have fewer than 2cq actual added edges relative to Q, and fewer than 2cq missing edges as well. The exact counts and the inequality d≥0 remain part of the statement. One also has the independent actual-path lower bound

Z(G)≥j(q−1−d)=j(q−j+δ).

At this linear scale Q is not asserted to be orthogonal. The Baer gap δ=0 or δ≥sqrt(q)/2 does not force δ=0 from δ<2cq. Orthogonality in Section 6 follows from equality in (3), not from that gap. The sub-square-root structural specialization may use the gap separately, but is not needed here.
