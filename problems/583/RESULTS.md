# Results and formal statements

All graphs are finite and simple. A path is nonempty and vertex-simple. `IsDecomposition G D` states that the members of D partition every original edge exactly. The type `V` may lie in any universe and has a `Fintype` instance.

## General connected graphs

`Erdos583.general_path_partition_improvement` in [Verified.lean](Erdos583/Verified.lean) has the statement

```lean
(G : SimpleGraph V) → G.Connected →
  ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, IsNonemptyPathSubgraph H) ∧ IsDecomposition G D ∧
    (D.card : ℚ) ≤ (2/3-1/654444 : ℚ)*Fintype.card V + 1/6 + 1/327222
```

There is no degree, density, parity or minimum-order hypothesis. This is an explicit original-edge partition, not a trail cover.

## Connected Eulerian graphs

`Erdos583.eulerian_path_partition_improvement` adds only the condition that every ordinary degree is even and concludes

```lean
HasPathBound G ((2/3-1/163611 : ℚ)*Fintype.card V + 1/54537)
```

`HasPathBound G b` asserts the existence of such a partition with cardinality at most b. Connectedness remains a hypothesis.

## Parity-sensitive baseline

`Erdos583.hasPathBound_phi` proves `HasPathBound G (phi G)` for every finite simple graph, including disconnected graphs and ambient isolates. The potential is u/2 + 2e/3, where u counts odd-degree vertices and e counts nonisolated even-degree vertices. This formalizes a classical baseline and is not claimed as a new contribution.

## Supporting statements

The complete source proves the restoration, endpoint, packing, parity and component facts used by these statements. Its [declaration inventory](scripts/headline-theorems.json) records every local declaration, type and axiom closure; the three statements above are the official oracle targets. Supporting declarations do not count as additional discoveries.

The manuscript's named lemmas refer to this same proof. Stronger written bounds and other unverified research conclusions are not included as new theorems in this package.
