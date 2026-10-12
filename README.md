# Erdős Problem 585

> What is the maximum number of edges that a graph on n vertices can have if it does not contain
> two edge-disjoint cycles with the same vertex set?
>
> [erdosproblems.com/585](https://www.erdosproblems.com/585) (Erdős problem; historical references are recorded on the linked problem page)

Hi, I'm Robert Huynh, currently a second-year MBA student at Harvard Business School. While
absolutely not a mathematician, I'm a founder and always excited to tackle new problems like this,
especially if I can use AI. I've spent these past few days attempting to see how far I can go
pointing a team of AI agents at this open problem. This repo holds what a team of agents plus me
steering has been able to do.

## Status

The problem is still open, as far as I know (October 2026). The known bounds on f(n), the maximum
number of edges of a graph on n vertices with no two edge-disjoint cycles on the same vertex set,
are f(n) ≥ c·n log log n (Pyber, Rödl and Szemerédi, 1995) and f(n) ≤ n (log n)^O(1) (Chakraborti,
Janzer, Methuku and Montgomery, Adv. Math. 2025; arXiv 2024). Below, two such cycles are called a
pair. Nothing in this repository changes either of those bounds.

This repo has 3 kinds of results: (1) results verified in Lean, (2) computer searches you can rerun,
and (3) written proofs that AI agents wrote and reviewed but no human has checked yet.

## Added in v0.4

The main additions concern q-regular subgraphs of finite simple bipartite graphs with maximum degree at most 2q − 2. Write D = (q − 1)n − e for the edge deficit, where n counts vertices and e counts unordered edges. A q-regular subgraph has degree q at each of its own vertices and can use only part of the original vertex set.

For every bipartite row below, q is an integer, n ≥ 2q and the maximum degree is at most 2q − 2. Each deficit condition guarantees a nonempty q-regular subgraph using original vertices and edges.

| Parameters | Sufficient deficit bound |
|---|---|
| Integer h ≥ 6, q ≥ 4096(h + 1)² | D ≤ hq − 16h² |
| q ≥ 2^18 = 262144 | D ≤ q^(3/2)/128 |
| q ≥ 36864 | D ≤ 5q − 58 |
| q ≥ 25600 | D ≤ 4q − 44 |
| q ≥ 16384 | D ≤ 3q − 32 |
| q ≥ 5 | D ≤ 2q − 5; this earlier theorem also gives some support of size at least 4q − 6 |

The fractional-power expression is real; since D is integral, its bound is equivalent to D ≤ floor(q^(3/2)/128). The v0.4 endpoints do not inherit the last row's larger-support guarantee. They assert neither a spanning nor an induced nor a connected subgraph. The endpoint declarations are `Erdos585.R898.every_h_forcing` and `Erdos585.R898.superlinear_forcing` in `R898/Main.lean`.

For every q ≥ 2^18, the parameterized theorem with h = floor(√q/64) − 1 permits a larger deficit than the real corollary, and for large q its allowance is about q^(3/2)/64. At q = 2^18 it permits h = 7 and deficit 7q − 784, while the real corollary states deficit 4q. The three earlier large-degree rows retain smaller cutoffs and remain useful.

The even-degree theorem for general finite simple graphs remains included: for even q ≥ 6, n ≥ 2, maximum degree at most 2q − 2 and D ≤ q − 2, some q-regular subgraph has at least 2q − 1 vertices. The quartic result gives a nonempty 4-regular subgraph in every bipartite graph with n ≥ 4, maximum degree at most six and e ≥ 3n − 6. Explicit examples at 3n − 8 exist for every n ≥ 11; whether 3n − 7 suffices in general remains open in this work.

An explicit family of avoiders shows that no allowance above q² − 3q + 3 can work, so for q ≥ 2^18 the best allowance lies between about q^(3/2)/64 and q² − 3q + 3; the open question is the exponent. For comparison, elementary bipartite completion and perfect-matching decomposition give a spanning q-factor at D ≤ q − 2. The leading allowance q^(3/2)/128 has a different growth rate, but concerns an extremely near-regular host class and permits selected support. The [literature comparison](literature/README.md) identifies precisely checked public statements; no direct derivation of the full endpoint was found in that bounded comparison. A worldwide novelty claim, a broadly new method and a separate new application have not been established.

The [mathematical note](findings/V0.4.md) gives exact hypotheses, source declarations and construction gaps. The [proof companion](findings/V0.4-PROOF.md) proves the classical factor step and one conditional union estimate, sketches the critical-support reduction, and gives a roadmap for the selection argument; normalization, peeling, the unequal-shore selector, common pins, hazard coverage and both cut-payment calculations are not proved in prose. It contains no written proof of the 5q − 58 theorem, QB(6) or the avoiding families; their evidence is the Lean sources and the checks. These are regular-subgraph bounds and formalizations related to Erdős 585. They do not give its required cycle pair or improve the known asymptotic bounds for f(n).

## Verified in Lean

The existing results below remain included. The additional v0.4 declarations are mapped in
[the mathematical note](findings/V0.4.md). Each result below compiles with no `sorry` and uses only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). Reproduce one with `./check.sh <file> <declaration>`.

| Result | Lean declaration |
|---|---|
| f(n) = n(n−1)/2 for n ≤ 4; f(5) = 9; f(6) = 12; f(7) = 16 | `Erdos585.maxEdges_eq_choose_two_of_le_four`, `Erdos585.maxEdges_five`, `Erdos585.maxEdges_six`, `Erdos585.maxEdges_seven` |
| f(n) ≥ 3n − 5 for n ≥ 7 (double wheel); f(n) ≥ 3n − 4 for n ≥ 9 | `Erdos585.three_mul_sub_five_le_maxEdges`, `Erdos585.three_mul_sub_four_le_maxEdges` |
| f(n+1) ≥ f(n) + 3 for n ≥ 3 | `Erdos585.maxEdges_succ_ge` |
| f(n) ≥ 4n − 13 for n ≥ 10; f(n) ≥ 5n − 15⌊√n⌋ − 10 for n ≥ 16 | `Erdos585.four_mul_sub_thirteen_le_maxEdges`, `Erdos585.five_mul_sub_sqrt_le_maxEdges` |
| f(11) ≥ 31, f(12) ≥ 36 | `Erdos585.thirty_one_le_maxEdges_eleven`, `Erdos585.thirty_six_le_maxEdges_twelve` |
| A 5-regular graph on 32 vertices with no such pair | `Erdos585.RegularFive.exists_five_regular_pairfree` |
| A bipartite 5-regular graph on 104 vertices with no such pair | `Erdos585.BipartiteFive.exists_bipartite_five_regular_pairfree` |
| A 5-regular graph on 18 vertices with no such pair | `Erdos585.RegularFive18.exists_five_regular_pairfree` |
| Every bipartite graph with maximum degree at most 6, n ≥ 3 vertices and at least 3n − 5 edges has a nonempty 4-regular subgraph | `Erdos585.qb5` |
| Every bipartite graph with maximum degree at most 6, n ≥ 2 vertices and at least 3n − 4 edges has a nonempty 4-regular subgraph (implied by the row above; it was proved first, and the proof of `qb5` builds on it) | `Erdos585.qb4` |
| For any bipartite 6-regular graph and any vertex v, the graph minus v still has a nonempty 4-regular subgraph (it has n − 1 vertices and 3(n − 1) − 3 edges, so this follows from the rows above) | `Erdos585.exists_four_regular_avoiding_of_bipartite_six_regular` |

All are in `Openmath/Proofs/Final.lean` except the three graphs
(`Openmath/Proofs/RegularFive18.lean`, `Openmath/Proofs/RegularFive.lean`,
`Openmath/Proofs/BipartiteFive.lean`, with edge lists in `graphs/` and a checker,
`graphs/verify_graphs.py`) and the three 4-regular subgraph results
(`Openmath/Proofs/QB4/Statement.lean`, `Openmath/Proofs/QB5/Statement.lean`).
`python3 scripts/check_axioms.py` checks the axioms and the recorded statement of every one at once,
together with the selected v0.4 additions listed in `scripts/headline-theorems.json`.
The expanded registry contains 76 declarations with checked printed types and permitted axioms: 25 carried
over from v0.3.1 and 51 added in v0.4, including 5 superseded, weaker versions of the two R898 endpoints (R866,
R874 and R882) retained for the record. Registrations include supporting statements and corollaries; they are
not a count of independent discoveries.

The 4-regular subgraph results are about 4-regular subgraphs, not pairs. Every pair is a 4-regular
subgraph (the union of its two cycles), but a 4-regular subgraph need not contain a pair, so these
results do not settle whether 6-regular graphs have a pair. For comparison, Remark 3.6 of Alon,
Friedland and Kalai (J. Combin. Theory Ser. B 37, 1984) gives a nonempty 4-regular subgraph in every
bipartite graph with maximum degree at most 7 and at least 3n − 2 edges. This is a comparison with one named published result, not a complete novelty assessment.
The [literature page](literature/README.md) records the scope and remaining source gaps. The
v0.4 quartic theorem reaches 3n − 6 edges for n ≥ 4. A computer search by two programs finds
that 3n − 7 edges are enough for 4 ≤ n ≤ 19; that finite computation does not settle the
remaining general threshold. The all-orders construction added in v0.4 supplies examples at 3n − 8
edges for every n ≥ 11.

QB(4), QB(5) and QB(6) are this project's labels (the number is the slack in 3n minus that
number, not a degree), and in the files under `QB4/` and `QB5/` a "pair" means a pair of vertex sets, not a pair
of cycles.

The linear lower bounds come from explicit constructions. For large n they are far below the known
lower bound of order n log log n.

## Computations

Exact values f(1), …, f(10) = 0, 1, 3, 6, 9, 12, 16, 19, 23, 27 were reported by
[Erdős Problem a Day](https://erdosproblemaday.com/report/585) on July 28, 2026
(read October 8, 2026). This repository reproduces those values. Programs and results are in
`computations/`; `computations/COMMANDS.md` gives the commands, outputs and upper-bound case checks.
The new computational entries beyond that report are f(11) = 31 and f(12) = 36;
the programs and logs are in `findings/supplement/small-values/`. The [saved upper certificates](findings/supplement/small-values/certificates/README.md)
now let a separate checker verify every positive rejection and every admissible extension.
The upper exclusions remain computational and share nauty's canonical generation;
separate certificate checking is not an independent graph census.

## Census

The three 5-regular graphs above show that being 5-regular does not force a pair, and the 18-vertex
one has the least order according to the reported complete census: no 5-regular graph on 16 or
fewer vertices is pair-free (through 14 by two separately written programs; at 16 by one complete
pruned search, with a second program on part of it). The tag includes the 20,000 completed shard
indices and aggregate records, but omits the raw per-shard logs and empty outputs. The complete
16-vertex exclusion has not had a complete independent replication. Its evidence is computational;
the 18-vertex witness itself is Lean verified. See `findings/supplement/census/`. Minimum degree alone never forces a pair: the Pyber, Rödl and
Szemerédi construction has no 3-regular subgraph and has order n log log n edges. It is pair-free:
a pair would give a 4-regular graph, and every 4-regular simple graph contains a 3-regular subgraph
(Read and Wilson, *An Atlas of Graphs*, Chapter 5, Theorem 11). Its growing average degree also
gives subgraphs of arbitrarily large minimum degree by repeatedly deleting vertices below half
the original average degree. I know of no result either way on whether every 6-regular graph has a pair.
The `census/` folder holds a computer search aimed at that case. Every graph with maximum degree at
most 6, minimum degree at least 4 and at least 3n − 4 edges was checked on 11 and 12 vertices, every
bipartite one on 13 to 18 vertices, and every 6-regular graph on 13 and 14 vertices. This was done
using nauty's `geng` to list graphs and the pair test in `census/programs/pairc.c`. We looked at
about 150 million of these graphs in all and every one of them had a pair. Every 6-regular graph is
in this class (it has 3n edges), so if that holds for every n, every 6-regular graph has a pair. I'm
keeping the search as evidence of this, not a proof, and it is weak evidence: the smallest pair-free
5-regular graph has 18 vertices and the smallest bipartite one I know of has 104, while the
6-regular search stops at 14 vertices and the bipartite search at 18. The commands are in
`census/programs/COMMANDS.md` and the logs are in `census/logs/`.

## Written proofs (AI-written and AI-reviewed)

I am looking for help with these. The written proofs are in `findings/`: AI agents wrote them and
other AI agents reviewed them, and no mathematician has checked them. If you work in extremal graph
theory and are willing to look at one, please open an issue.

`findings/FINDINGS.md` lists every result in this repo with its evidence (Lean, computation, or
written proof), the files behind it, and the checks I most need an expert's help with (section 6).
The main written candidates:

- Every bipartite 6-regular graph on at most 24 vertices has a pair. This rests on three written
  proofs and four computer searches, three of them done by two separately written programs.
- Every graph with maximum degree at most 6, n ≥ 2 vertices and at least 3n − 2 edges has a nonempty
  4-regular subgraph (from the Lean result above and Tutte's f-factor theorem).
- "Every bipartite 6-regular graph has a pair" is equivalent to its vertex-deleted form: every
  bipartite 6-regular graph minus any one vertex has a pair.
- If every bipartite 6-regular graph has a pair, then f(n) is of order n log log n (an immediate
  consequence of Pyber, Rödl and Szemerédi, 1995, and Janzer and Sudakov, Forum Math. Pi 2023).
- If every bipartite regular graph on N vertices with degree at least a constant times (log N)^3 has
  a pair, then f(n) = O(n (log n)^4), directly from Theorem 1.5 of Chakraborti, Janzer, Methuku and
  Montgomery, "Regular subgraphs at every density" (Trans. Amer. Math. Soc. 2026).

How they were reviewed: each written proof was reviewed by at least one separate AI agent in a fresh
context, and the reviewer reran any computation with its own code. The reviewer was often the same
model as the author, so some proofs got a second or third reviewer, including one on a different
Claude model (Fable 5.1 reviewing work by Opus 5.5). Section 7 of the findings lists the models
behind each part of the work through v0.4, including the reviews. AI review is a filter, and AI reviewers can
miss errors, so none of this is verified yet. That's why I'm seeking help. The supplement
(`findings/supplement/`) keeps the proofs and reviews as they were written, with every later edit
recorded.

## The formal statement

`Openmath/Target.lean` is the statement I proposed to
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures). It
defines `maxEdges` and the pair predicate used above. No human Lean expert has reviewed it yet. If
it is merged, this repository will import the upstream statement instead.

## How this was made

I pointed AI agents (OpenAI's GPT-6 Astra and GPT-6.1 Sol, and Anthropic's Claude Fable 5.1 and Claude Opus 5.5) at
the recent literature to find techniques that might apply to Erdős 585. The agents proposed ideas,
wrote proofs and search programs, and reviewed each other's work. The Lean results were also checked
by the Lean kernel, and the exact values were cross-checked by separately written programs. Between
passes I steered them back toward the main question when they tunneled into dead ends or into
methods that would cost more than my budget allowed, and I made sure we had checkpoints and new
directions to try.

Most of my steering was setting the rules for what counts as progress and pushing the agents toward
novel approaches. First, I set the rules for what actually counted. A Lean result counted only when
`check.sh` passed: the build has no `sorry` and uses only the 3 standard axioms. For QB(5), a
separate agent also compared the Lean statement with the written one, and separate reviewers checked
every row of the "Verified in Lean" table against its Lean statement. In the later passes, every
main written claim needed either a Lean proof or a review by a separate agent in a fresh context,
and results for fixed sizes were recorded as fixed-size results, never as the general case. For the
key computer searches I asked for a second, separately written program, and the findings say which
searches have one. In the last pass, long computations ran as a small pilot first, with a budget cap
and a stop command. I tracked what each pass cost (section 8 of the findings has the figures),
parked directions that were not paying off, and had the agents keep a private, dated log of my decisions. A digest of those decisions is in
[findings/DECISIONS.md](findings/DECISIONS.md).

Second, I kept pushing the agents to look at the math literature and at other AI-assisted math
research for related results and methods they could apply here, instead of starting from scratch.
For example, the conditional route in the findings goes through a recent theorem of Chakraborti,
Janzer, Methuku and Montgomery on regular subgraphs.

## AI use

The formal statements, Lean proofs, written proofs, constructions and search programs in this
repository were produced with AI agents; section 7 of `findings/FINDINGS.md` says which model did
what. I read the results, the checks and the claims they support.

I'm an MBA candidate at Harvard Business School, not in a mathematics program, and I did not check
the mathematics myself. I take full responsibility for any errors. No mathematician has reviewed the
mathematics yet, although I am looking for help: if you find an error or know of prior work, or are
willing to help, please open an issue and I'd love to get in contact with you.

The [literature comparisons](literature/README.md) identify earlier mathematics behind
the existing results and credit Alejandro Zarzuelo Urdiales's dated public literature and proof-coverage review.

## Build

Needs elan (Lean's installer), Python 3.11 or later for the checks and the computations, GNU `timeout`
(coreutils) for the commands as written, and a C compiler with nauty 2.9.3 only for the census. Build time varies by machine and cache state.
Downloading the pinned Mathlib cache avoids rebuilding Mathlib from source. Run these commands
from the repository root:

**Formal verification.** On October 11, 2026 the 437 configured custom modules (of the tree's 496 Lean files; the others are Axioms.lean, which check_axioms.py runs, and 58 supplement files under findings/supplement/lean/, which this run did not build) were rebuilt from an empty custom-module cache; `scripts/check_axioms.py` matched the printed types of the 76 registered declarations against the recorded ones (a string match on printed types, which pins the declaration names but not the bodies of the project definitions that some types mention) and confirmed that only the three standard axioms are used; the 75 `./check.sh` calls for the registered proved declarations returned `RESULT: PASS`; and LeanChecker, the kernel replay tool shipped with the Lean v4.33.1 toolchain, replayed every configured custom module. An earlier run the same day, on the tree before the comment-only header corrections and before the circular family was registered, gave the same results for its 75 declarations (its receipts are private). The transcript of the final run is in `findings/supplement/checks/v0.4/`. The commands below reproduce each kind of step; the loop under "Check theorem results" in .github/workflows/ci.yml runs all 75 ./check.sh calls. Each `./check.sh` call ends with a line beginning `RESULT: PASS`, and `check_axioms.py` ends with `AXIOMS: PASS (76 proved declarations)` and `STATEMENTS: PASS (76 recorded types)`. One registered declaration in `Openmath/Target.lean` has type/axiom and kernel evidence but no whole-file oracle call because that file also contains unproved conjectures. The conjectures remain unproved, and no registered proved result depends on `sorryAx`. Dependency caches were reused; this was not a from-empty Mathlib rebuild. These checks establish neither novelty, complete prose exposition nor human mathematical review.

```bash
timeout 900 lake exe cache get
timeout 1800 lake build
timeout 240 ./check.sh R898/Main.lean Erdos585.R898.superlinear_forcing
timeout 240 ./check.sh R898/Main.lean Erdos585.R898.every_h_forcing
timeout 240 ./check.sh R831/Endpoint.lean Erdos585.H5BareR831.bare_h5_original_caller
timeout 240 ./check.sh Openmath/Proofs/Final.lean Erdos585.maxEdges_seven
timeout 240 python3 scripts/check_axioms.py
# kernel replay of every configured custom module, one module per call (about an hour at 2 threads)
python3 -B scripts/source_modules.py --list | while IFS= read -r m; do
  printf 'import LeanChecker\n#eval replayFromImports "%s".toName\n' "$m" | timeout 240 lake env lean --stdin
done
# optional: rebuild every custom module from scratch, then rerun the checks above
rm -rf .lake/build && timeout 1800 lake build
```

## License and citation

Apache-2.0 (see `LICENSE` and `NOTICE`). To cite this work, see `CITATION.cff`.
