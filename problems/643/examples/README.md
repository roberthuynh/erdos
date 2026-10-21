# Explicit finite examples

These files check three concrete hypergraphs from the manuscript's examples appendix using only Python's standard library and exact rational arithmetic. They do not prove the universal inequality, classify its equality cases or verify its Lean statement.

The complete vertex and edge lists are in [da2-host.json](hosts/da2-host.json), [cone3-host.json](hosts/cone3-host.json) and [cone4-host.json](hosts/cone4-host.json). [check_examples.py](check_examples.py) reads those lists directly. It imports no campaign engine, private file or third-party package. [generate_examples.py](generate_examples.py) independently expands the displayed construction patterns into those lists. There are no network calls or hidden inputs.

## Replay

Replace placeholders with absolute paths. Run from any working directory:

```sh
timeout 240 python3 -I <EXAMPLES_PATH>/check_examples.py
```

Look for `"result": "PASS"`. The observed output is [results.json](results.json), with the actual portable command and environment recorded in [receipt.json](receipt.json). To regenerate the exact labelled hosts, choose a directory that does not exist:

```sh
timeout 240 python3 -I <EXAMPLES_PATH>/generate_examples.py <NEW_HOST_DIRECTORY>
timeout 240 python3 -I <EXAMPLES_PATH>/check_examples.py --data <NEW_HOST_DIRECTORY>
```

A failed check exits nonzero. Acceptance uses explicit exceptions, so optimized Python does not disable these tests. `SHA256.json` pins every supplied source, host list and receipt except the manifest itself.

## Definitions checked directly

For each pair of disjoint edges the checker records its six-vertex union and rejects a collision with another disjoint edge pair. Two different such pairs cannot share one edge, since the other edge would be its complement in the same union; a collision therefore supplies four distinct edges. Separately, it constructs each vertex link from the explicit triples, intersects the two links for each apex pair, and checks that every two pairs in that common link meet. This directly checks both the original forbidden configuration and its common-link characterization on these finite hosts.

The shadow is the set of pairs contained in an edge. The co-link set consists of apex pairs with a nonempty common link. For every edge, the checker sums reciprocal pair codegrees for sigma and `1/(2*common_link_size)` over its actual options for tau, then computes `c = sigma + tau - 2`. It also verifies the global charge-sum identity. Triangular common links and active bicones are determined from the explicit triples and computed negative charges.

A four-edge forbidden configuration is rejected by both tests. A cone with two apexes has Phi = -1 and is rejected as an equality example. These are bounded negative controls, not a proof for arbitrary hosts.

## Two cone equality examples

`cone_k` has a three-vertex base and k apexes; its edges are all base pairs extended by one apex.

| Host | Vertices | Edges | Shadow pairs | Co-link pairs | Phi | Every edge charge |
|---|---:|---:|---:|---:|---:|---:|
| cone_3 | 6 | 9 | 12 | 6 | 0 | 0 |
| cone_4 | 7 | 12 | 15 | 9 | 0 | 0 |

Both attain `2|H| = |shadow| + |CL(H)|`. Neither attains `|H| = binom(n,2)`: their edge counts are 9 versus 15 and 12 versus 21, respectively. Each edge has sigma `1+1/k`, tau `1/k+(k-1)/6`, and charge zero for k = 3,4. The program checks these quantities for every edge; it makes no general equality classification claim.

## A deficient DA2 host with a tight local branch

The seven singleton vertices a,b,c,w,t,r,z and classes X,Z,E,Y of sizes 9,26,19,17 give 78 vertices and 1,307 edges. Each listed pattern selects one vertex from each of its three classes:

```text
abc acw abt atw btw bcw bcr brz crz cwz bwz abz
abX bXw bcZ bXZ abE bEr bEZ bzZ bwY bYZ
```

For apexes c,t, base a,b,w and anchor bcw, the explicit checker obtains:

| Quantity | Exact value |
|---|---:|
| c(abc) | -409/755160 |
| c(acw) | 1/2 |
| c(bcw) | 367/1566 |
| Deficit at apex c | 409/755160 |
| Active bicones containing bcw | {c,t} and {w,r} |
| Activity of bcw | 2 |
| k(b,w) | 29 |
| (n_B,n_C,m,m_prime) | (1,0,1,0) |
| W_minus | 7/12 |
| X_cost | 5/12 |
| H_w = tau_W | 1/12 |
| c(bcw)/2 - deficit | 792709/6796440 |
| c(bcw) - 2*deficit - 1/29 | 675529/3398220 |

The W quantities are recomputed from explicit slot groups, relation neighbours and reciprocal slot costs; tau_W is evaluated from its stated piecewise formula. This realizes the local W equality coordinate with a deficient edge and two active anchor incidences. Both displayed anchor margins are positive. It is not a global equality example: shadow = 1,382, co-link = 1,539 and Phi = -307. Its 1,307 edges also fall below binom(78,2) = 3,003. No limiting-rate or universal anchor claim follows from one host.

## Provenance and license

[source-provenance.json](source-provenance.json) records original witness/generator/engine source identities and the explicit relabelling. The exported DA2 edge set was checked exactly against the retained original construction after that relabelling. The portable checker was written from the literal definitions and uses the same rational quantities, without importing the original engine. This is an executable finite check, not an independent human proof review. Sources follow the collection's Apache-2.0 license.
