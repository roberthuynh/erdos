> AI-written exposition. The main result has [Lean verification](VERIFICATION.md); this does not certify every written intermediate statement. No human mathematical review is claimed.

# Degree-capped core and retained paths

Use the single support and simultaneous bounds of [linear localization](LINEAR-SUPPORT-THEOREM.md).

## 1. One enlarged support, including actual degree capping

The original high-degree surplus is P<=20T. Process original high vertices and delete incident edges while their current degree exceeds q+1. This constructs one actual edge set D_cap of size at most P; degree can only decrease, so the final graph has maximum degree at most q+1.

Let S_1 consist of S_0 together with every endpoint of every edge in D_cap. Write m=|S_1|. Then

  m<=252T+2P<=292T.

Define F by deleting ALL E(G[S_1]) from G. Because this includes E(G[S_0]), F is C4-free. Because it includes D_cap, F has maximum degree at most q+1. It is essential to include D_cap: deletion of E(G[S_0]) alone was not proved to cap original high degrees.

Every vertex outside S_1 retains all its incident edges. The original set S_0 contains all high and all deficit-at-least-two vertices. Thus every outside vertex has degree q or q+1 in both G and F. The original bound d_G(v)>=q+1−26T gives

  minimum degree(F)>=q−318T.

Originally there are at least N−|{d_G<=q}|−|{d_G>=q+2}| degree-(q+1) vertices, which is at least q²+2−40T. Excluding S_1 leaves at least

  q²+2−332T                              (C1)

unchanged full-degree vertices in F. Their neighborhoods are actual distinct sets of size q+1, and any two intersect in at most one point because F is C4-free.

No edge-loss bound of order q for F is assumed. The removed induced graph can have many more than q edges, so this construction alone does not put F in HMY's stability window.

## 2. Conditional completion pays the missing-edge support

Assume for the rest of this section that a polarity graph Q of order q contains F. This assumption is supplied by [the count-based completion theorem](COUNT-BASED-COMPLETION.md). All subsequent conclusions are deductions from this assumption and the actual input.

Every edge of G with an endpoint outside S_1 lies in F and hence Q. Consequently all added edges

  J=E(G)\E(Q)

lie entirely inside S_1. Write j=|J|.

We next locate the missing Q-edges, rather than bounding them by the potentially large total |E(G[S_1])|. An outside vertex has degree q or q+1 in G and retains all its edges in F. In any polarity graph every degree is q or q+1. Therefore an outside vertex can have a missing incident Q-edge only if its degree in G is q and its degree in Q is q+1; in that case it has exactly one missing incident Q-edge.

Every polarity graph of order q has at least q+1 absolute vertices, of degree q. At least q+1−m of these are outside S_1, and each is necessarily a degree-q vertex of G. The total number of deficient vertices in G is at most q−1+20T. Hence the number of outside vertices upgraded from degree q in G to q+1 in Q is at most

  (q−1+20T)−(q+1−m)=m+20T−2.

If the displayed lower count of outside absolute points is negative the estimate would be vacuous; here m<=292T<q, so it is positive. Thus the number of missing Q-edges having at least one outside endpoint is at most m+20T. Every such edge is counted by at least one upgraded outside vertex, and each such vertex accounts for only one edge. Missing edges with two outside endpoints may be counted twice, which only weakens this upper bound.

## 3. Retained paths through every actual added edge

Fix ab in J. Its endpoints lie in S_1. The polarity lemma supplies at least q−1 simple length-three Q-paths from a to b, pairwise edge-disjoint for this fixed pair.

Missing Q-edges entirely inside S_1 destroy at most 2m of these paths. Indeed, any path using such an edge has at least one of its two internal vertices in S_1. Each core vertex can occur as the first internal vertex in at most one path, since otherwise the two paths share its edge to a. It can occur as the second internal vertex in at most one path, since otherwise the edge to b is shared. The endpoints a,b never occur as internal vertices of these simple paths. Thus at most 2m paths have an internal core vertex at all. This bounds simultaneously the endpoint-edge and middle-edge types of missing internal edges; no matching surrogate is used.

The at most m+20T missing Q-edges with an outside endpoint destroy at most m+20T additional paths, by edge-disjointness. Therefore ab lies in at least

  q−1−3m−20T >= q−1−896T                    (C2)

actual cycles of G, each with exactly one J-edge.

Across different ab in J, these counted cycles are distinct because each has exactly one edge outside Q. Hence

  Z>=j(q−1−896T).                           (C3)

In the stated numerical range q−1−896T>q/2. Since Z<Tq, this gives

  j<2T.

Deleting the actual set J makes G a subgraph of Q and therefore C4-free. Thus J hits ALL original cycles, including those with two or more J-edges; the proof never assumes those cycles are absent. Conditional on completion, an actual global cover of fewer than 2T edges has been established, despite possibly many missing Q-edges inside the core.
