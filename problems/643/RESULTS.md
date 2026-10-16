# Result index: Erdős 643

For every finite vertex set V of size n and every family H of three-element subsets of V avoiding that configuration,

$$|H| \le \left\lfloor \frac{4}{3}\binom{n}{2} \right\rfloor.$$

There are no additional density, codegree or structural hypotheses. The bound includes all nonnegative orders n. The maximum avoiding size therefore satisfies the same bound; the minimum forcing threshold is at most that integer plus one. The Lean theorem proves the per-family inequality. Extremal and forcing functions are written corollaries, not separate formal declarations.

| Item | Evidence |
| --- | --- |
| Main declaration | [`Erdos643.FinalBound.card_le_floor_four_thirds`](Openmath/Erdos643/FinalBound.lean) |
| Complete project-source closure | 11 files, individually hashed in [source-identity.json](source-identity.json) |
| Verification scope | [Verification record](VERIFICATION.md) |
| Original conjecture | Open; this is a partial bound |
| Novelty and human review | Not established |

The claim in this package is the coefficient bound stated above.
