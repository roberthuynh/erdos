> AI-written exposition. The main result has [Lean verification](VERIFICATION.md); this does not certify every written intermediate statement. No human mathematical review is claimed.

# Linear-parameter localization of actual cycle-cover edges

## Statement

Let q>=10^16 be even, let 1<=T<=10^(−8)q be real, and let G be a simple graph on N=q²+q+1 vertices with M+1 edges, where M=q(q+1)²/2. If G has Z<Tq copies of C4, then there is a set S_0 of at most 252T vertices such that the actual set E(G[S_0]) meets EVERY C4 of G.

The following simultaneous properties are available from the same construction. Put f(v)=max(q+1−d(v),0), H={d>=q+2}, and S={f>0}. Then

  P=sum_{v in H}(d(v)−q−1)<=20T,
  q−5T<=|S|<=q−1+20T,
  sum_{v in S}(f(v)−1)<=25T,
  f(v)<=26T.

Every vertex has at most 50T neighbors in S, except possibly one vertex z with more than q−76T such neighbors. Set

  X={c(v)>4q/5} union H union {f(v)>=2} union {z}.

Here c(v) is the number of actual C4s containing v; z is omitted if absent. Then |X|<=51T. Let R consist of vertices outside X that have an opposite mate outside X, where opposite means at least two common neighbors in G. Then |R|<ceil(200T)<=201T, and S_0=X union R has the asserted cover property. These are definitions and conclusions on one graph, not individually selected supports.

## Proof dependencies and full parameter audit

The algebraic and combinatorial proof is [the localization argument](LOCALIZATION-ARGUMENT.md). This extension uses every inequality there up to the support bound, but does NOT use its comparison 31752T²<q/16 or any subsequent application of stability. The wider range must be checked separately, as follows.

1. Maximum degree. In that proof the endpoint polynomial for k>=T+3 has value q²−T²/2−3T/2−2 at k=T+3, and value q⁴/2−q³−(T+1/2)q²+(T+3)q−2 at k=q². For q>=10^16 and T/q<=10^(−8), both exceed 2Tq. Concavity therefore gives d<q+T+3 exactly as before.

2. Preliminary high rows. The two nonopposite high-row cases give 2Z at least q²/10−21q/10−1 or 3q²/5−3q/5−6. Each exceeds q²/20, whereas 2Z<2Tq<=2\*10^(−8)q². Thus low-cycle high rows are pairwise opposite, and h<=1+2sqrt(Tq)+20T<=3sqrt(Tq). The last inequality follows from 20sqrt(T/q)<=0.002 and sqrt(Tq)>=10^8. In particular h/q<=3\*10^(−4)<1/10.

3. Deficient count and all-high summation. The inequality h/(q+1)<=T follows from h<=3sqrt(Tq), T>=1, and q>=10^16. Hence |S|>=q−5T. The same exact all-high inequality holds:

  (q−h−1)P<=4Tq+q+h²/2+sqrt(2)h sqrt(Tq)+5hT.

Its right side is at most 14.25Tq and its left coefficient at least 0.8q, using h<=q/10. Thus P<=20T, and all the displayed degree-deficit consequences follow without a T²/q condition.

4. Neighborhood dichotomy. The original product contradiction needs q>=1000T. This holds because T/q<=10^(−8). At the two endpoints b=50T and b=q−76T, the products 30T(q−76T) and 50T(q−96T) exceed 12Tq. Uniqueness of z follows because binom(q−172T,2)>Tq in this range. Therefore the same 50T / (q−76T) dichotomy holds.

5. Deep-deficit exclusion and transport. The set X has size at most 51T. Outside X, degree is q or q+1. The actual local proof gives c(u)+2c'(v)>=q−175T for every ordered opposite pair outside X, with c'(v) the number of cycle-containing neighbors of v. Since q>=1750T, it yields c'(v)>=q/20. No stronger relation between T and q was used in this step.

6. Aggregate selection. With ell=ceil(200T)<=201T, inclusion-exclusion and the exact global codegree budget give

  |union_i (N(v_i) intersection C_\*)|
    >=10Tq−20201T²−285T sqrt(Tq).

The error divided by Tq is at most

  20201\*10^(−8)+285\*10^(−4)=0.02870201<1.

Thus ell distinct outside-X opposite endpoints would force more than 9Tq cycle-containing vertices, contradicting |C_\*|<=4Z<4Tq. So |R|<ell.

7. Actual support. If a C4 has adjacent X vertices, their edge lies in E(G[X union R]). Otherwise the cycle has zero, one, or two opposite X vertices. With zero, all its vertices lie in R. With one, its two cycle neighbors have opposite mates outside X and lie in R. With two opposite X vertices, the remaining pair lies in R. In every case an actual cycle edge is in E(G[X union R]). This proves the cover assertion, including cycles that leave S_0.

This audit checks every numerical use of the former square-root bound before the support-cost step. The only discarded conclusion is the cheap bound on the number of all internal edges; their trivial bound remains 31752T², which need not lie in the polarity-stability radius for the wider range.
