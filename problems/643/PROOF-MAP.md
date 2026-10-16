# Formal proof map

The [parent theorem](Openmath/Erdos643/FinalBound.lean) proves the original-pattern inequality for every finite family. The imports form an 11-module closure, all frozen in [source-identity.json](source-identity.json).

| Stage | Source | Role |
| --- | --- | --- |
| Exact configuration | [HypergraphBasics](Openmath/Erdos643/HypergraphBasics.lean) | Four distinct triples, disjoint pairs, equal union; exact six-vertex support |
| Graph deletion | [GraphDeletion](Openmath/Erdos643/GraphDeletion.lean) | PV Lemma 3 supplier, including zero remaining common neighbors for original diagonals |
| Private pairs | [PrivatePairs](Openmath/Erdos643/PrivatePairs.lean) | PV Lemma 7 separation |
| Exceptional five-sets | [K5Local](Openmath/Erdos643/K5Local.lean), [K5Cleaning](Openmath/Erdos643/K5Cleaning.lean) | Actual deletion and the PV Lemma 11 budget |
| Triangle cleanup | [TriangleCleanup](Openmath/Erdos643/TriangleCleanup.lean) | Makes every common link a star, charging at most one third of the diagonal budget |
| Projection | [Projection](Openmath/Erdos643/Projection.lean), [ProjectionBridge](Openmath/Erdos643/ProjectionBridge.lean) | Three flags per triple; exact unordered pair identities |
| Owner deletion | [DegreeCharge](Openmath/Erdos643/DegreeCharge.lean), [AllStarDeletion](Openmath/Erdos643/AllStarDeletion.lean) | Pays deletion cost and leaves at most one root for each pair |
| Composition | [FinalBound](Openmath/Erdos643/FinalBound.lean) | Combines proved suppliers, then derives the integer floor bound |

The final hypotheses are only Uniform H and absence of the original forbidden configuration, on a finite vertex type. The all-star and cleaning hypotheses are discharged inside the proof. No extra axiom supplies the published lemmas. The [written proof](PROOF.md) gives the parallel counting argument.
