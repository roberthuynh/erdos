# Erdős #60: result index

[Overview](README.md) · [Findings](FINDINGS.md) · [Verification](VERIFICATION.md)

The results below have Lean proofs checked by this package. They were produced and reviewed by AI agents; no human mathematical review or worldwide priority clearance is claimed.

| Result | Exact statement and Lean declaration | Scope |
|---|---|---|
| Exact C4 supersaturation | [Written theorem](LINEAR-RANGE-THEOREM.md), §§1, 4–6; [power_two_c4Supersaturation](ExtremalHeadline.lean) | Powers of two q≥10^16; integers 1≤t≤10^-8 q; h(q²+q+1,t)=t(q−1), counting ordinary unlabelled C4 copies. |
| Universal even-order lower bound | [linear_range_lower](LinearRangeHeadline.lean) | Every simple graph on q²+q+1 vertices with M+t edges, M=q(q+1)²/2, has at least t(q−1) C4 copies for even q≥10^16 and integer 1≤t≤10^-8 q. |
| Matching equality classification | [linear_range_equality_iff](EqualityHeadline.lean) | Under the same even-order hypotheses, equality holds exactly for an orthogonal polarity graph with a matching of t edges added between absolute vertices. Attainment is not asserted at every even order. |
| Exact extremal threshold | [power_two_c4Extremal](ExtremalHeadline.lean) | ex(q²+q+1,C4)=M for powers of two q≥10^16. This known extremal value is formalized here to establish the exact h interpretation. |
| First-excess polarity edit structure | [Written theorem](LINEAR-RANGE-THEOREM.md), §7; [first_excess_structural](FirstExcessHeadline.lean) | Even q≥10^16, real 1≤T≤10^-8 q, M+1 edges and Z<Tq; j≤Z/(q−1−896T)<2T, δ=M−e(Q)≥0 and d=j−1−δ≥0 for a polarity Q on the same vertices. Orthogonality is not asserted. |

The combined powers-of-two conclusion is also registered as `Erdos60.Headline.power_two_extremal_and_supersaturation`. The six main declarations received official `RESULT: PASS` checks; the separate complete kernel replay and type/axiom audit are recorded in [Verification](VERIFICATION.md).

These results do not settle unrestricted Erdős #60 or the entire q/2 conjectural surplus range. [The source comparison](LITERATURE-COMPARISON.md) records bounded inspection and unresolved journal-version/priority limits. [Citation metadata](CITATION.cff) identifies the unpublished result and formalization; include the exact source snapshot.
