# Proof map

Each path names executable Lean source. The 103 source files form the union of the five main import closures. The hash inventory is in [source-identity.json](source-identity.json).

## Fractional upper bound

1. [Basic](Erdos1017/Basic.lean) defines nonnegative clique masses and exact original-edge loads. [CliqueLaw](Erdos1017/CliqueLaw.lean) aggregates finite distributions into graph partitions.
2. [ProductSelector](Erdos1017/ProductSelector.lean), [RootedSelector](Erdos1017/RootedSelector.lean), and [GraphSelector](Erdos1017/GraphSelector.lean) construct independent selectors and their graph realizations.
3. [HigherTrades](Erdos1017/HigherTrades.lean), [CombinedTrades](Erdos1017/CombinedTrades.lean), and [TradeParameters](Erdos1017/TradeParameters.lean) preserve individual and pair moments while bounding all negative withdrawals.
4. [LogEnclosure](Erdos1017/LogEnclosure.lean), [ProductEnclosure](Erdos1017/ProductEnclosure.lean), and [ContinuousCertificate](Erdos1017/ContinuousCertificate.lean) provide rational bounds. The latter imports the complete set of rational cell batches, from [Batch00](Erdos1017/RectangleCells/Batch00.lean) through [Batch23](Erdos1017/RectangleCells/Batch23.lean). [RectangleAffine](Erdos1017/RectangleAffine.lean) turns those bounds into partition costs.
5. [TrianglePacking](Erdos1017/TrianglePacking.lean), [LocalTriangleLeave](Erdos1017/LocalTriangleLeave.lean), [TypeInflation](Erdos1017/TypeInflation.lean), and [MultipartiteWeights](Erdos1017/MultipartiteWeights.lean) cover the other part-size ranges and complete induction on the part index type. [TypeLift](Erdos1017/TypeLift.lean) preserves every original edge when passing to graph cliques.
6. [WeightedGraph](Erdos1017/WeightedGraph.lean), [WeightMerge](Erdos1017/WeightMerge.lean), [WeightedClique](Erdos1017/WeightedClique.lean), and [WeightedSymmetrization](Erdos1017/WeightedSymmetrization.lean) implement weight transfer on the unchanged graph. [SharpAffine](Erdos1017/SharpAffine.lean) sets vertex weights to one.

## Prescribed-edge lower bound

[MesoscopicGraph](Erdos1017/MesoscopicGraph.lean) defines the four-part graph. [MesoscopicCounts](Erdos1017/MesoscopicCounts.lean) counts its actual unordered edges. [MesoscopicDual](Erdos1017/MesoscopicDual.lean) proves the signed certificate for all clique sizes and converts integral partitions into fractional ones. [MesoscopicParameters](Erdos1017/MesoscopicParameters.lean) controls the integer part sizes. [MesoscopicInterpolation](Erdos1017/MesoscopicInterpolation.lean) attains every eligible edge count. [MesoscopicLower](Erdos1017/MesoscopicLower.lean) combines those results and retains all finite error terms.

## Binomial-cost extrema

[BinomialDefs](Erdos1017/BinomialDefs.lean) defines product demands, exact partitions, covers and costs. [BinomialReduction](Erdos1017/BinomialReduction.lean) transfers integer weights between nonadjacent vertices. [BinomialSelector](Erdos1017/BinomialSelector.lean) supplies every required higher inclusion moment; [BinomialCount](Erdos1017/BinomialCount.lean) bounds its cost. [BinomialUpper](Erdos1017/BinomialUpper.lean) gives the all-graph upper bound. [BinomialLower](Erdos1017/BinomialLower.lean) counts t-cliques meeting the independent side of a split graph. [BinomialSharp](Erdos1017/BinomialSharp.lean) chooses a maximizing split graph and proves equality.

## Further bounds

[SplitDual](Erdos1017/SplitDual.lean) supplies a signed lower bound on split graphs; [SlopeBarrier](Erdos1017/SlopeBarrier.lean) chooses integer parameters that defeat every larger anchored slope. [DenseWeights](Erdos1017/DenseWeights.lean) and [NearComplete](Erdos1017/NearComplete.lean) implement the separate weighted argument for the near-complete upper bound.
