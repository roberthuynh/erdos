> AI-written exposition. The main result has [Lean verification](VERIFICATION.md); this does not certify every written intermediate statement. No human mathematical review is claimed.

# Localization argument

The following is the full elementary argument through the actual vertex support. Its original parameter range is q≥10^16 and 1≤T≤10^(-4)sqrt(q), with q even; [the linear parameter audit](LINEAR-SUPPORT-THEOREM.md) verifies every needed inequality for 1≤T≤10^-8 q. The induced-edge cost bound and subsequent stability argument are not used. The aggregate-overlap and selection arguments are included here in full.

## 1. Exact notation and path inequalities

For the cover theorem fix a single actual G with e(G)=M+1 and Z<Tq. Write d(x) for degree, c(x) for the number of C4s containing x, d(x,y) for common-neighbor count, and d_0(x) for the number of distinct vertices having no common neighbor with x. Then

  c(x)=sum_{y!=x} binom(d(x,y),2),   sum_x c(x)=4Z.

Put f(x)=max(q+1−d(x),0), S={x:f(x)>0}, H={x:d(x)>=q+2}, h=|H|, and P=sum_{x in H}(d(x)−q−1). The exact total deficiency is

  B=sum_x f(x)=q−1+P.                       (1)

For any vertex x, the actual two-path count gives

  c(x)>=(d(x)−q−1)q−f(N(x))+d_0(x).         (2)

Indeed sum_{y!=x}d(x,y)=sum_{w in N(x)}(d(w)−1)>=d(x)q−f(N(x)); and sum binom(d(x,y),2)>=sum(d(x,y)−1)+d_0(x).

If d(x)>=q+1 and N(x) avoids S, then c(x)>=1. Otherwise (2) forces d(x)=q+1 and d_0(x)=0. Every neighbor of x then has a common neighbor with x, so G[N(x)] has no isolated vertex. If c(x)=0 it has maximum degree one, since any two-edge path there gives a C4 through x. It would therefore be a perfect matching on the odd number q+1 of vertices, impossible. This is the only parity input before final stability.

For every vertex subset A, grouping two-paths by endpoints gives

  2Z >= sum_x binom(|N(x) intersection A|,2)−binom(|A|,2).       (3)

For any nonnegative integer r and integer b>=0,

  binom(r,2)>=binom(b,2)+b(r−b),             (4)

because the difference is (r−b)(r−b−1)/2. We use (4) without an assumption on the average degree.

Finally, for any m distinct vertices x_i, with K=binom(m,2),

  sum_{i<j} d(x_i,x_j)<=K+2sqrt(KZ).         (5)

This follows from sum over all unordered pairs of binom(d(x,y),2)=2Z, the integer inequality a<=1+sqrt(2binom(a,2)), and Cauchy–Schwarz. Thus all overlaps, not selected witnesses, are charged to the same host's cycles.

## 2. Maximum degree for the whole parameter range

Suppose d(v)=q+k. For i!=v put a_i=|N(i) intersection N(v)|. Since c(v)<Tq,

  sum_{i!=v}a_i<=q²+(T+1)q.

Take A=V\N(v) in (3), omit the zero contribution at v, and apply (4) with b=q−1 to the N−1=q²+q remaining values d(i)−a_i. Their sum is 2e(G)−d(v)−sum a_i. Expansion yields

  2Z >= q³−2q²+2q−(q−1)sum a_i
         −k²/2+k(q²−q+3/2)−2
      >= F(k),

where

  F(k)=(k−T−2)q²+(T+3−k)q+3k/2−k²/2−2.

For T+3<=k<=q² this concave quadratic is minimized at an endpoint. At k=T+3 its value is q²−T²/2−3T/2−2. At k=q² its value is q⁴/2−q³−(T+1/2)q²+(T+3)q−2. Under the stated q,T range both exceed 2Tq. This contradicts 2Z<2Tq. Therefore

  d(x)<q+T+3,  and  d(x)−q−1<T+2 for x in H.                 (6)

For example all these comparisons already follow from q>=10^16 and T<=10^(−4)sqrt(q), which imply T<=q/100 and q sufficiently large for the displayed endpoint bounds.

## 3. Preliminary high-vertex count, including both union cases

Two distinct high vertices u,v satisfying c(u),c(v)<q/5 must be opposite, meaning d(u,v)>=2.

Suppose instead that their common-neighbor count is at most one. Write d(u)=q+1+p_1, d(v)=q+1+p_2 and D=p_1+p_2. By (6), 2<=D<2T+4. Put B_\*=N(u) union N(v) and a_i=|N(i) intersection B_\*| for i distinct from u,v.

If u,v have a unique common neighbor w, then

  d(u,i)+d(v,i)=a_i+1_{i adjacent to w}.

Using binom(r,2)>=r−1 separately for the two codegrees and summing over i!=u,v gives

  sum_{i!=u,v}a_i+d(w)<=2q²+2q+c(u)+c(v)
                         <2q²+(12/5)q.

Take A=V\B_\* in (3), discard the contributions at u,v,w, and apply (4) with b=q−1 to the remaining r_1=q²+q−2 values. Their sum is at least r_1(q−1)−D−2−(2/5)q. Also |A|=q²−q−D. Consequently

  2Z >= r_1 binom(q−1,2)
        −(q−1)(D+2+(2/5)q)−binom(q²−q−D,2).                 (7)

As an integer function of D in [2,2T+4], the right side increases: its successive difference is q²−2q−D. Its value at D=2 is q²/10−21q/10−1.

If u,v have no common neighbor, the same summation instead gives

  sum_{i!=u,v}a_i<=2q²+2q−2+c(u)+c(v).

Now discard just u,v, so r_0=q²+q−1 and |A|=q²−q−1−D. The sum of the remaining values is at least r_0(q−1)−q+1−D−(2/5)q. Hence

  2Z >= r_0 binom(q−1,2)
        +(q−1)(−q+1−D−(2/5)q)−binom(q²−q−1−D,2).           (8)

This increases with D too; its successive difference is q²−2q−D−1. At D=2 its value is 3q²/5−3q/5−6.

Both (7) and (8) exceed q²/20 for the stated parameters, contradicting 2Z<2Tq. This proves the assertion, including the disjoint-neighborhood case.

There are at most 20T high vertices with c(x)>=q/5. If there are k other high vertices, every pair is opposite, so binom(k,2)<=2Z and k<=1+2sqrt(Tq). Therefore

  h<=1+2sqrt(Tq)+20T<=3sqrt(Tq).             (9)

The last inequality holds throughout our numerical range. In particular h<=q/10.

## 4. Degree-excess localization by summing all high rows

There are N−h−|S| degree-(q+1) vertices. At most q|S| of them have a neighbor in S, since every S vertex has degree at most q. Every remaining one has c(x)>=1 by Section 1. Thus

  N−h−(q+1)|S|<=4Z<4Tq,
  |S|>=q−5T.                               (10)

Here (9) implies h/(q+1)<=T. It follows that

  E:=B−|S|<=P+5T.                          (11)

For any vertex set U, f(U)<=|U intersection S|+E. Sum (2), with d_0 omitted, over ALL h high vertices. Inclusion-exclusion on their actual neighborhoods inside S, followed by (5), gives

  qP <=4Tq+|S|+binom(h,2)+2sqrt(binom(h,2)Z)+hE.

Using |S|<=B=q−1+P and (11),

  (q−h−1)P <=4Tq+q+h²/2+sqrt(2)h sqrt(Tq)+5hT.              (12)

This is the point at which summing all preliminary high rows is useful: the term hP is absorbed on the left, rather than bounded by a crude preliminary estimate for P.

By h<=3sqrt(Tq), h<=q/10, T>=1 and q large, the right side of (12) is at most

  (4+1+4.5+4.25+0.5)Tq=14.25Tq,

where 3sqrt(2)<4.25. The coefficient q−h−1 is at least 0.8q. Thus

  P<=20T,  h<=20T,
  B<=q−1+20T,
  E<=25T,
  f(x)<=25T+1<=26T.                        (13)

In particular there are at most 25T vertices with f(x)>=2, since each contributes at least one to E=sum_{x in S}(f(x)−1). No exact integer bound P<=2T+2 is asserted or needed.

## 5. Deficient-neighborhood dichotomy

For a vertex v put b=|N(v) intersection S| and list its r=d(v)−b nondeficient neighbors v_i. Let N_i=N(v_i)\\{v}. Every N_i has size at least q. Each overlap vertex of two N_i contributes the actual C4 v-v_i-x-v_j-v, so inclusion-exclusion gives

  |union_i N_i|>=qr−c(v)>=qr−Tq.             (14)

Let C_i consist of vertices of N_i lying in no C4 of G. These sets are pairwise disjoint. At most |S|<=q+20T vertices of their union lie in S. Every x in C_i\S has some neighbor in S, by Section 1, and that neighbor lies outside N(v): otherwise there is a C4 through x. For each fixed i, distinct x in C_i\S cannot share such a neighbor, since that would give a C4 with v_i. Therefore

  |C_i\S|<=|S\N(v)|<=q+20T−b,
  |union_i C_i|<=r(q+20T−b)+q+20T.

There are at most 4Z<4Tq vertices lying in any C4. Combining this with (14) gives

  r(b−20T)<=5Tq+q+20T<=12Tq.                (15)

But r>=q−26T−b by (13). If 50T<=b<=q−76T, the concave product (q−26T−b)(b−20T) is minimized at an endpoint, where its values are 30T(q−76T) and 50T(q−96T), respectively. Both exceed 12Tq in our range. Consequently every vertex has

  b<50T  or  b>q−76T.                      (16)

There is at most one vertex z of the second type. Otherwise two such vertices have at least q−172T common neighbors in S, giving at least binom(q−172T,2)>Tq cycles. If no such vertex exists, all later mentions of z are omitted.

## 6. Remove deep-deficit rows from the transport problem

Let A be the vertices with c(x)>4q/5, and let D be the vertices with f(x)>=2. Define

  X=A union H union D union {z}.

By sum c=4Z and (13),

  |X|<=5T+20T+25T+1<=51T.                  (17)

For every vertex outside X its degree is q or q+1. This simultaneous exclusion of D is what makes the transport coefficient below independent of T.

Take any ordered opposite pair (u,v) with both endpoints outside X. Put a=f(u), so a is either zero or one, and let V_u be the vertices having no common neighbor with u. By (2), (13), and (16),

  |V_u|<=c(u)+aq+f(N(u))<=c(u)+aq+75T.       (18)

Partition N(v) as follows:

  N_1=N(v) intersection S;
  N_2=N(v) intersection N[u];
  N_3={x in N(v)\\(N_1 union N_2): |N(x) intersection V_u|<=a};
  N_4=N(v)\\(N_1 union N_2 union N_3).

Although N_1 and N_2 can overlap, the stated set containments and bounds below do not require them to be disjoint. We have |N_1|<=50T. Every vertex of N_2 lies in a C4, since u,v are opposite (including u itself if adjacent to v).

Every x in N_3 also lies in a C4. Each vertex in N(x)\V_u has a neighbor in N(u), and v has at least two such neighbors. Thus the number of edges from N(x) to N(u), counted with those actual endpoints, is at least

  d(x)−|N(x) intersection V_u|+1>=q+2−a.

This exceeds |N(u)|=q+1−a. Hence some y in N(u) has two distinct neighbors in N(x). Since x is outside N[u], y!=x, and these two neighbors give a C4 containing x. All four vertices are distinct in the simple graph.

Let C be the neighbors of v lying in no C4. The preceding paragraph shows C is contained in N_1 union (N_4 intersection C). For distinct x,x' in C, the sets N(x) intersection V_u and N(x') intersection V_u are disjoint: a shared point other than v makes a C4 through x, and v is not in V_u because u,v are opposite. Each x in N_4 intersection C contributes at least a+1 such points. Therefore

  |N_4 intersection C|<=|V_u|/(a+1).

Writing c'(v) for the number of neighbors of v lying in any C4, and using d(v)>=q,

  c'(v)>=q−50T−(c(u)+aq+75T)/(a+1).

It follows that

  c(u)+2c'(v)>=q−175T.                     (19)

Here a+1<=2 and c'(v)>=0. Since u is outside A and q>=1750T, we conclude

  c'(v)>=q/20.                             (20)

The inequality holds for every ordered opposite pair outside the one fixed set X; no row-specific host or independently chosen repair is involved.

## 7. Aggregate selection gives a cover of all cycles

Let ell=ceil(200T)<=201T. Suppose there were ell distinct vertices v_i outside X each having an opposite mate outside X. Choose any such mate u_i for each; the u_i need not be distinct. By (20), each actual set N(v_i) intersection C_\* has size at least q/20, where C_\* is the set of all vertices lying in a C4. It has size at most 4Z.

Inclusion-exclusion and (5) give

  |union_i (N(v_i) intersection C_\*)|
     >=ell\*q/20−binom(ell,2)−2sqrt(binom(ell,2)Z)
     >=10Tq−20201T²−285T sqrt(Tq).

The numerical range implies 20201T/q+285sqrt(T/q)<1. Thus this union has more than 9Tq vertices, contradicting |C_\*|<=4Z<4Tq.

Let R be the set of vertices outside X having an opposite mate outside X. We have proved |R|<ell. The ACTUAL edge set

  E(G[X union R])                           (21)

meets every C4. To check all supports, take a cycle. If it has adjacent X vertices, their edge is in (21). Otherwise it has zero, one, or two X vertices, with any two opposite. With zero, all four cycle vertices have opposite mates outside X and lie in R. With one, the two cycle neighbors of its X vertex form an opposite pair outside X, hence lie in R, and the incident cycle edges are covered. With two opposite X vertices, the other two vertices lie in R and all cycle edges join X to R. These cases include every cycle, without classifying how many edges are outside any proposed polarity.
