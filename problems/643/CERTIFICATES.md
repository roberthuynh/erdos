# Computational certificate specification

The finite checks certify the domains below. The host-to-profile implications, feasibility conditions, analytic tails and redistribution estimates are mathematical proof obligations; a finite output does not replace them. The separate coefficient-one package now verifies the exact full theorem and its dependency chain. Historical computational output and equality-enumeration claims retain their stated scopes.

| Claim | Exact finite domain and target | Inspectable command/output |
|---|---|---|
| C1 | Nonnegative type counts tA,tB,tC with sum≤11; six relation counts in {0,…,92}; feasibility (F); profile≥23/12. The implementation uses target 23/12 for t≤1 and the stronger target 2 for t≥2. | `check_profiles.py box`, [box output](computations/results/0-check_profiles.py.json); four t≤1 cases also in [integer output](computations/results/4-c1_integer.py.json). |
| C1g | For 2≤t≤11, profile≥2; for t=1, each of three type-slot positions and V1–V4 noncompliant classes, with partner constraints, profile≥2. | Same box command: 364 type triples plus 12 position/class calls, 376 cases total. |
| C2 | Four rest counts in {0,…,92}, relevant feasibility, type sum≤11; tail expression≥11/12. Each kappa minimum includes zero and integers p=23,…,160. | `check_profiles.py tail`, [tail output](computations/results/1-check_profiles.py.json). |
| C2g | Same rest domain; strengthened target 1 for t≥2 and each noncompliant t=1 position. | Same tail command: 364 type triples plus three noncompliance calls, 367 cases total. |
| W | 0≤nB,nC≤11, 1≤m+m′≤6; A1–A3 from the written proof; corrected gap≥0. | `check_additions.py`, [corrected output](computations/results/5-check_additions.py.json): 3,279 points; unique zero (1,0,1,0). |

## Arithmetic and infinite tails

The primary checker floors rational terms at scale 2^40. Signed int64 min-plus arithmetic supplies lower enclosures, then inclusive pruning retains all candidates at or below the target for exact Fraction evaluation. Integer-range bounds and sentinel separation are explained in the [computation specification](computations/README.md). The separate C1 t≤1 implementation uses Python integers at scale 2^32, rational matrix construction and forbidden entries represented by None. It certifies a lower bound, not the exact minimum or all minimizers. Its author inspected the primary implementation and shares its cycle method; this is not blind or conceptually independent review. The historical C1 t≤1 cross-check used rigorous directed floating-point rounding; that older method is not relabelled as integer-only.

The written reduction treats t≥12, two large relations, and one-sided counts≥93 analytically. The cutoff 92 cannot replace 93 for the threshold-two step: S(92,22,11)=4232/2127<2, whereas S(93,22,11)=8649/4300>2. For the one-big-relation tail, u≤103 and s≤11; the kappa numerator at x=161 is at least 6434 and increasing afterwards. Thus p>160 cannot lower its minimum with zero. These analytic statements must hold universally, separately from scanning the retained domain.

## Target equalities, not auxiliary minima

The box and tail outputs include complete `target_equality_vectors`, their coordinate order, type counts, target and class context. Inclusive pruning retains every true equality at the tested threshold. The recorded target-2 box total is 41 profiles among 20 type triples; the tail totals are two at target 11/12 and eight at target 1. These statements refer to the exact implemented domains and outputs. They are not a claim that relaxed tail parameters can all be simultaneously realized in one host.

The larger historical C1 minimum, the claim of exactly six minimizers, and larger C1g/C2g class minima are omitted. Their separate branch-and-bound sources and full-domain receipts are not supplied and are unnecessary for the threshold proof. No optional completeness claim is inferred from the threshold scans.

The historical `check_wbox.py` evaluates 3,401 points, including 122 points in an impossible mutual variant and a second zero. It is retained for reproducibility, not used as the corrected domain's equality classification. The corrected domain has 3,279 points and is checked separately.

## Reproduction and output identity

Use the exact environment/setup and commands in [computations/README.md](computations/README.md), with a result directory that does not exist. The runner rejects any existing directory, including one holding an old success. Each child has a 240-second limit. Timeouts produce UNKNOWN with partial logs; other failures produce FAIL. Failed runs do not create a new replay success receipt. See the evidence ledger for actual runs; a documented command alone is not a receipt.

Runtime-bearing raw output hashes need not repeat. [Semantic hashes](computations/results/semantic-hashes.json) recursively omit only `seconds` and `elapsed_seconds`, then hash sorted compact UTF-8 JSON with ensure_ascii=False. List order, rational strings and every non-timing field remain. [Source manifest](computations/SHA256.json) identifies exported files. Neither normalization nor a package PASS verifies the full theorem.

## Explicit hosts illustrating the boundary

The [generator](examples/generate_examples.py) and [checker](examples/check_examples.py) operate on supplied explicit triples, with [recorded exact results](examples/results.json), an [actual command receipt](examples/receipt.json) and [construction provenance](examples/source-provenance.json). For DA2 the coordinates are (nB,nC,m,m′)=(1,0,1,0), the anchor has activity two, and H_w=tau_W=1/12. The recovery margin c(A)/act(A)−D is 792709/6796440>0; the stronger margin c(A)−act(A)D−1/k_uw is 675529/3398220>0. This is local W equality with strictness elsewhere, not equality in the global theorem or proof of an asymptotic family.

Cone_k consists of a fixed base triangle and, for each of k apexes, its three triples with the base pairs. For cone3, (vertices,triples,shadow,colink)=(6,9,12,6); for cone4 the counts are (7,12,15,9). Every charge is zero and 2|H|=|∂H|+|CL(H)|. Neither has |H|=binom(n,2). These explicit examples refute an identification of shadow/co-link equality with K5 unions; they do not classify all equality hosts.
