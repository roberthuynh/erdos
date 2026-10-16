# Erdős #585: result index

[Collection](../../README.md) · [Problem overview](README.md)

This index points to the existing mathematical statements and evidence. It adds no result and does not settle the original cycle-pair problem or improve its known asymptotic bounds.

| Work | Statements and evidence | Limits |
|---|---|---|
| Near-regular bipartite q-regular subgraphs, including parameterized and fractional-power bounds | [v0.4 note](findings/V0.4.md), [v0.4.1 corrections and checks](findings/V0.4.1.md), [registered declarations](scripts/headline-theorems.json) | Selected support; neither spanning, induced nor connected is asserted. Read exact cutoffs and deficits. |
| Small exact values, explicit lower-bound constructions and regular pair-free witnesses | [Lean results](README.md#verified-in-lean), [witness checker](graphs/verify_graphs.py) | Formal statements and permitted axioms are distinct from novelty and human review. |
| Finite exact-value searches and upper certificates | [commands and coverage](computations/COMMANDS.md), [certificate guide](findings/supplement/small-values/certificates/README.md) | Upper exclusions are computational and share canonical generation; certificate checking is not an independent census. |
| Regular-graph census | [census account](README.md#census), [commands](census/programs/COMMANDS.md) | Finite coverage; complete 16-vertex exclusion has no complete independent replication. |
| Written and conditional arguments | [findings](findings/FINDINGS.md), [written-proof account](README.md#written-proofs-ai-written-and-ai-reviewed), [proof companion](findings/V0.4-PROOF.md) | AI-written and AI-reviewed as described there; no human mathematical review is claimed. The companion does not expand every Lean argument. |
| Prior-work comparison | [literature guide](literature/README.md) | Bounded comparison, with remaining source and priority limits. |

Registered verification inventory: 78 registered declarations, 77 whole-file oracle checks, 438 configured custom modules.

See [build instructions](README.md#build) for historical verification scope and current commands. Cite the [problem-specific citation](CITATION.cff), plus the exact declaration or written source used. `R643.lean` is a #585 module, not a release of Erdős #643.
