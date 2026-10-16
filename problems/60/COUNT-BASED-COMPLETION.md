> AI-written exposition. The main result has [Lean verification](VERIFICATION.md); this does not certify every written intermediate statement. No human mathematical review is claimed.

# Count-based completion of an even-order near-projective graph

Source interfaces are listed in [Sources](SOURCES.md).

## Contract

Let q be an even integer with q≥10^8, and let F be a simple C4-free graph on N=q²+q+1 vertices. Suppose

* .999q≤d(v)≤q+1 for every vertex;
* S={v:d(v)≤q} has size at most 1.001q;
* D={v:d(v)≤q−1} has size at most .001q.

Then F is a spanning subgraph of a polarity graph of a projective plane of order q.

The hypotheses bound counts of deficient vertices and the minimum degree rather than total edge deficiency. Deleting all induced edges of a core gives only a crude quadratic budget, not an established quadratic-loss example under these hypotheses. The proof constructs one simultaneous point-to-line bijection and retains every actual edge.

## 1. Basic C4-free facts and a bounded exceptional set

Distinct vertices have at most one common neighbor. Consequently an induced neighborhood has maximum degree one, and for N(v)={v_i}, the cells N_i=N(v_i)\N[v] are pairwise disjoint. The bundles N_i∪{v_i} are also pairwise disjoint.

Every full vertex (degree q+1) has a neighbor in S. Otherwise its q+1 neighbors all have degree q+1, producing (q+1)q=N−1 two-step paths with distinct endpoints other than the vertex. Thus every other vertex, including every neighbor, is reached. The induced neighborhood would be a perfect matching on the odd number q+1 of vertices, impossible.

Set B={v:|N(v)∩S|≥q/100} and A={v:d(v)=q+1}\B. Counting pairs of S with their common neighbor gives

|B| binom(q/100,2)≤binom(|S|,2),

where the real binomial on the left is a valid lower bound. For q≥10^8 this gives |B|≤11000. Thus

|A|≥q²−.001q+1−11000.                                      (1)

Call z regular if z is full and its neighbors consist of q full vertices and one degree-q vertex.

## 2. Exact structure and transport at a regular vertex

Let z be regular and label its q+1 neighbors z_i. The cells C_i=N(z_i)\N[z] are disjoint and lie in a set of size q²−1. The degree sum of the neighbors is q²+2q. If e_z is the number of edges in N(z), then

Σ|C_i|=q²+q−1−2e_z≤q²−1.

Since e_z≤q/2, equality holds: e_z=q/2, and the cells partition V\N[z]. Thus the local graph is a matching of size q/2 and one isolated vertex.

The isolated neighbor is the degree-q neighbor. Here is the needed count-based proof, rather than an invocation with hidden global deficiency assumptions. If the low neighbor z_1 were paired with z_2 and the isolated neighbor were full, then |C_1|=q−2, the q−1 other matched cells have size q−1, and the isolated cell has size q. For each matched full index i other than 2 (there are q−2 such indices), write m=|C_i|=q−1. There are no edges between C_i and its paired cell. Edges inside C_i form a matching, hence contribute at most m−1 to the degree sum. Edges to each other cell form a matching; there are q−1 eligible other cells, with one further loss because C_1 has size m−1. Edges to N[z] contribute exactly m. Therefore

Σ_{w∈C_i}d(w)≤m+(m−1)+(q−1)m−1=(q+1)m−2.

So the total deficiency in each such cell is at least two. At most |D| cells meet D. Every remaining such cell therefore contains at least two vertices of S. Their disjointness would imply

|S|≥2(q−2−|D|)≥1.998q−4>1.001q,

a contradiction.

We now have the following exact transport fact. If u is full, u∉N[z], and u is adjacent to a full neighbor z_1 of z, then

|N(u)∩N(z_i)|=1 for every i.                               (2)

Indeed, let z_1z_2 be the matching edge. The unique neighbor of u in N(z) is z_1. It has no neighbor in C_2, since such a neighbor would make a C4 through z_1z_2. It has at most one neighbor in each other cell. Its q+1 neighbors force equality in each of these q cells, plus z_1. This proves (2), including index 2 via z_1.

## 3. Many regular neighbors and exact intersection of full rows

For x∈A put S_x=N(x)∩S and S_x^\*=S_x∪(N(S_x)∩N(x)). Then |S_x^\*|≤2|S_x|<.02q. Every z∈N(x)\S_x^\* is full, and all its low neighbors lie in its cell N(z)\N[x]. Every such cell contains at least one low vertex by Section 1. At most |D| of these disjoint cells meet D. Among the remaining k≥q+1−.02q−.001q cells, a neighbor is regular exactly when its cell contains one low vertex; otherwise it contains at least two. If p of these neighbors are regular, then

2k−p≤|S|,

so p≥.957q+2. In particular x has more than q/100+1 regular neighbors.

We prove that N(x) and N(y) intersect for all distinct x,y∈A. Suppose they do not. If xy is an edge, choose a regular z∈N(x) other than y. Then y∉N[z] and y is adjacent to the full neighbor x of z; (2) contradicts disjointness.

Otherwise xy is not an edge. For every regular z∈N(x), y∉N[z]. The exact partition from Section 2 places y in a cell indexed by a neighbor w of z, so yw is an edge. If w were full, (2), applied at z with u=y adjacent to the full neighbor w of z, would give |N(y)∩N(x)|=1 because x is also a neighbor of z, again contradicting disjointness. Hence w must be the unique degree-q neighbor of z. Distinct regular z in N(x) give distinct w: a repeated w creates the actual C4 x-z-w-z'-x. Therefore |N(y)∩S| exceeds q/100, contradicting y∈A.

Thus R={N(x):x∈A} consists of distinct (q+1)-sets with every pair intersecting in exactly one point. Distinctness also follows from C4-freeness.

## 4. The actual projective plane

Apply the published Metsch embedding theorem (HMY 2023, Theorem 2.1): a 1-intersecting (q+1)-uniform hypergraph on N points embeds in a projective plane if q≥3900 and its number of lines exceeds

q²−((sqrt(5)−1)/2)q+17 sqrt(q/5).

Bound (1) exceeds this for every q≥10^8. We obtain a plane P on these same N points containing R. Put R^c=P\R. Then

|R^c|=N−|A|≤1.001q+11000≤1.002q.                          (3)

Only existence is needed. No claimed symmetry precedes the point-to-line assignment below.

## 5. A high-incidence neighbor of every vertex

Every vertex v has a neighbor u incident with at least q−2 lines of R, equivalently |N(u)∩A|≥q−2.

To prove this, take the disjoint bundles N_i∪{v_i} of Section 1. Exclude bundles meeting D or B, at most .001q+11000 bundles. At least .998q−11000 bundles remain. If every remaining bundle contained at least two vertices of S, disjointness would give |S|≥1.996q−22000>1.001q. Choose a remaining bundle containing at most one low vertex. It has no deep vertex, so its total deficiency is at most one, and it has no B vertex. For u=v_i,

|N(u)∩A|≥|N_i∩A|≥d(u)−2−|N_i∩S|
             ≥q−1−f(u)−f(N_i)≥q−2.                       (4)

Here f(w)=q+1−d(w); only this selected bundle has its deficiency bounded. No bound on total deficiency is used.

## 6. Every neighborhood is collinear apart from one common point

A vertex v is feasible if N(v) is contained in a line of P. For a non-feasible v, every line containing two points of N(v) belongs to R^c: otherwise the row N(a) would give a C4, and a=v would instead make v feasible.

Choose u∈N(v) as in (4). At most three lines of R^c pass through u. The non-feasible neighborhood is partitioned by α∈{2,3} such lines, apart from their common point u. Let the sizes outside u be a_1≥a_2≥a_3≥0, with only α positive entries. Their sum is d(v)−1≥.999q−1, so a_1≥(.999q−1)/3. For i≥2, the a_1 a_i cross-pairs belong to distinct lines of R^c: a line other than either pencil line meets each of them in at most one point. Hence a_1 a_i≤1.002q. At q≥10^8 this implies a_i≤3. The largest pencil line L_v therefore contains at least d(v)−6 points of N(v).

For every w∈N(v)\L_v, the lines joining w to these at least d(v)−6 collinear points are distinct members of R^c. If two distinct exceptional points w,w' occur, whether for the same vertex or different vertices, their two line families each have size at least .999q−6 and overlap in at most one line. Their union would have size at least 1.998q−13>1.002q, contradicting (3).

Consequently either all vertices are feasible, or there is a single point w such that every vertex v has an associated line L_v containing N(v)\\{w}. For feasible vertices choose their containing line. Each such line is unique, since the retained neighborhood has at least .999q−1>1 points. Distinct vertices have distinct associated lines: otherwise their retained neighborhoods, whose intersection has size at most one, would occupy at least 2(.999q−1)−1>q+1 points on one line. Thus v↦L_v is a bijection from the N points to the N lines. For a∈A, L_a=N(a).

## 7. Symmetry and containment without an edge-loss budget

Let M be the actual plane incidence matrix under that bijection, with M_ab=1 iff b∈L_a. Every row and every column has q+1 ones. For a∈A\\{w}, if M_ab=1, then b∈N(a), hence a∈N(b)\\{w}⊆L_b and M_ba=1. Equality of row and column sums makes the entire row and column symmetric, including all cross-block entries.

There are at least |A|−1>q²−q+3 such indices. Simultaneously reorder points and assigned lines to place these indices first. The partial-symmetry theorem (HMY 2023, Lemma 2.1, originating in Füredi) implies M is symmetric. The bijection is therefore a polarity.

Every edge ab of F with b≠w satisfies b∈L_a. Edges with b=w satisfy a∈L_w because a≠w, and symmetry supplies w∈L_a. If no exceptional point exists, containment is immediate. Thus every actual edge of F lies in the simple polarity graph. This proves the contract.

## 8. Application to the linear support construction

Use [linear localization](LINEAR-SUPPORT-THEOREM.md) and the explicit [degree-cap/core construction](CORE-AND-RETAINED-PATHS.md).

For even q≥10^16, 1≤T≤10^-8 q, e(G)=M_q+1 and Z<Tq, they give a core S_1 of size at most 292T such that F=G−E(G[S_1]) is C4-free, Δ(F)≤q+1 and δ(F)≥q−318T. Moreover

|{d_F≤q}|≤|{d_G≤q}|+|S_1|≤q−1+312T,

and every deeply deficient vertex of F lies in S_1: all original deeply deficient vertices were included in the original support. Therefore |{d_F≤q−1}|≤292T. These satisfy the contract with ample slack. Hence F is contained in a polarity graph Q.

The [retained-path argument](CORE-AND-RETAINED-PATHS.md) is now applicable: if j=|E(G)\E(Q)|, then

Z≥j(q−1−896T),

and therefore j<2T. In particular the j actual edges outside Q form a global C4 cover of G, including cycles with two or more such edges. This establishes the completion needed for the global cycle cover. It does not assert that an induced-core cycle cover alone covers the original graph.
