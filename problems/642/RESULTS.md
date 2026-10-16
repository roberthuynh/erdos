# Result index: Erdős 642

There is an absolute constant C > 0 such that every finite simple graph G on n vertices satisfying

$$e(G) > C n\bigl(\log(2n)\bigr)^5$$

contains an actual simple cycle with at least its length in distinct actual chords. The logarithm is natural. The same C works for every graph and every order; no regularity, expansion or spectral hypothesis remains in the final theorem. At n=0 the Lean expression uses Real.log 0 = 0 and the strict edge condition is impossible; the empty and singleton cases are vacuous. The theorem does not provide a useful small numerical C.

| Item | Evidence |
| --- | --- |
| Main declaration | [`Erdos642.CampaignFe72210bContinuation3.OriginalBound.original_log_five_rich_cycle`](Openmath/Erdos642/Proofs/CampaignFe72210bContinuation3/OriginalBound.lean) |
| Complete project-source closure | 134 files, individually hashed in [source-identity.json](source-identity.json) |
| Verification scope | [Verification record](VERIFICATION.md) |
| Original conjecture | Open; this is a partial bound |
| Novelty and human review | Not established |

The claim in this package is the fifth-power threshold stated above.
