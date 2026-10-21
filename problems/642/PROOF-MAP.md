# Proof map

The main declaration is `Erdos642.Log3V1_20261024.original_log3_rich_cycle`. Its conclusion uses the actual graph edges and an actual simple cycle. The route below introduces no extra hypothesis on the input graph.

| Step | Mathematical role | Source |
|---|---|---|
| Cycle and chord definitions | Count distinct original unordered edges on the cycle support. | [CycleSupport](Openmath/Erdos642/Proofs/CampaignFe72210b/CycleSupport.lean), [SpectralHost](Openmath/Erdos642/Proofs/CampaignFe72210b/SpectralHost.lean) |
| Host extraction | Find an injectively embedded bipartite host with controlled degrees and cuts. | [Extract](Openmath/Erdos642/Proofs/Log3V1_20261024/Extract.lean) |
| Dense mask | Choose a set with at least twice the host order in induced edges, while controlling each vertex's neighborhood in the mask. | [MaskCore](Openmath/Erdos642/Proofs/DenseMask20261019/MaskCore.lean) |
| Fresh layers and Hall injections | Supply disjoint tough layers and inject endpoint occurrences into each layer. | [LayerHall](Openmath/Erdos642/Proofs/Log3V1_20261024/LayerHall.lean) |
| Paths through tough graphs | Apply the proved Gallai path theorem to the port sets. | [ToughPaths](Openmath/Erdos642/Proofs/Log3V1_20261024/ToughPaths.lean) |
| Merging and cycle closure | Merge a fixed fraction of components per layer and close the resulting path. | [Merger](Openmath/Erdos642/Proofs/Log3V1_20261024/Merger.lean) |
| Parameters | Choose absolute constants in an order that meets all inequalities. | [Constants](Openmath/Erdos642/Proofs/Log3V1_20261024/Constants.lean) |
| Original graph theorem | Compose the steps and transport the cycle and chords back to the input graph. | [Theorem](Openmath/Erdos642/Proofs/Log3V1_20261024/Theorem.lean) |

The formal interfaces appear in [Interface](Openmath/Erdos642/Proofs/Log3V1_20261024/Interface.lean). The fourth-power theorem supplies growth for avoiding subgraphs. The previous fifth-power proof guide remains in [PROOF.md](PROOF.md). The six supporting facts and their exact declarations appear in [RESULTS.md](RESULTS.md).

`Openmath.lean` imports all 263 proof modules. The module inventory and declaration registry specify the scope of the portable checks, including dependencies that are not listed individually in this map.
