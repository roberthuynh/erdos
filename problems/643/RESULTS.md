# Result index: Erdős 643

| Claim | Scope | Evidence boundary |
|---|---|---|
| 2&#124;H&#124;≤&#124;∂H&#124;+&#124;CL(H)&#124; | Every finite simple avoiding 3-graph; literal original four triples | Exact unconditional Lean theorem verified; human review open. |
| &#124;H&#124;≤binom(n,2) | Every such host, including n=0 | Exact unconditional Lean corollary verified. |
| f(n;3)=ex₃(n)+1≤binom(n,2)+1 | Minimum forcing threshold; distinct from maximum avoiding size | Exact forcing-threshold Lean corollary verified. |
| f(n;3)=(1+o(1))binom(n,2) | n→∞, using classical lower construction | Unconditional Lean asymptotic corollary, including the formal lower construction; no novelty claimed for the classical construction. |
| Classical K5-filled S(2,5,n) examples and exact extremal/forcing values | Every natural n≡1 or5 (mod20), including n=1: ex₃(n)=binom(n,2) and f(n;3)=binom(n,2)+1 | General design existence, construction and exact values are Lean-verified. The classical construction is attributed to Füredi and Hanani. No equality classification, stability or novelty of the construction is claimed. |
| cone3 and cone4: shadow/co-link equality | Explicit 6/7-vertex hosts with 9/12 triples | [Exact checks](examples/results.json); every initial charge zero; neither meets binom(n,2). No classification claimed. |
| DA2: tight local W-box point | One 78-vertex, 1,307-triple avoiding host, activity two | [Explicit host/checks](examples/results.json); local W equality, strictly positive final anchor margin; no global equality. |
| Historical 4/3 | Original avoiding condition, finite orders | Existing sources/summary concern this older theorem only. |
| Development 9/8 and 24/23 | Intermediate formal bounds, not coefficient one | Exact source/receipt/export scope in [Verification](VERIFICATION.md), including the separately executed 20-module standalone build and actual-upstream 24/23 bridge. |

[Certificate thresholds](CERTIFICATES.md) are distinct from optional exact minima, which are omitted. Equality in the shadow/co-link inequality is not equivalent to equality in the cardinality bound. No t≥4 result, first-priority claim or complete classification is asserted.
