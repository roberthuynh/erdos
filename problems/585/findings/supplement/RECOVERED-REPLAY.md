# Recovered inputs and bounded replays

These are finite computational checks of supplied data. They do not establish the all-sizes Erdős 585 theorem, certify every historical computation, or provide Lean verification. Existing mathematical limitations in REPRODUCTION-BOUNDARY.md continue to apply.

## Inputs

The five QB5 graph6 classes (orders 11 through 15) are in `papers/qb5/original-inputs/`. The recovered pairs review sources and text outputs are in `papers/pairs/review/code/`; compiled executables are excluded. The original erroneous marked-pair program is retained as `census/pairs-lane/mpair.c` solely to identify the historical bug. Use `papers/pairs/review/code/mpair_fixed.c` for the corrected implementation. The historical `t1_res.txt`, `t2_res.txt`, and NONE streams are not corrected certificates.

The three original validation modules are bundled under `census/programs/gen585/validation_tools/`. The recovered S6 programs and historical outputs are under `papers/s6/review/`, with the certificate in `papers/s6/data/pg25_depth4.json`. PROVENANCE.json maps original recovered-source hashes to current bytes; changes are limited to public relative-path wording and portable entrypoint configuration. Archived review judgments refer to their original bytes, not automatically to these edited copies.

## Executed checks

All individual replay commands were bounded by 240 seconds and completed. Logs in `replay/` are new execution records, separate from the historical outputs.

| Check | Observed result | Scope |
|---|---|---|
| Independent rpair controls | 407 cases, zero mismatches, 84 pairs | Finite controls, not parser fuzzing or a proof of the implementation |
| Corrected T2 enumeration | 66,992 rows; 66,986 have three pairings and six have two | Exact multiset equality with all archived corrected `t2census/part_*.out` rows; all six exceptions have 12 vertices |
| Historical 82 NONE answers | All 82 have independently checked realised witnesses | Refutes those historical labels; does not replace every original census stream |
| Fixed mpair bug controls | 18 rows, all NONE | Supplied bug-test inputs |
| gen585 controls | 600 graphs, zero disagreements, 352 PAIR and 248 NOPAIR | Supplied test_pair control suite |
| gen585 level 8 | 4,738 canonical avoiders from each method; zero duplicates and empty symmetric difference | N=13, EF=35, SP=5, SPMIN=2, MINDF=4, level=8, emin=14, emax=19 only |
| FINAL validator controls | K5 gives valid PAIR certificates in both methods; K4 gives NOPAIR in both | Artificial controls with EF/minimum-degree 10/4 and 6/3 respectively; K4 is not a counterexample to the target theorem |
| QB5 petal checks | Class sizes 2, 13, 29, 818, 2,895; zero sparsity failures | Full supplied five classes; n15 has three bad ports, so no all-ports claim |
| Independent QB5 c2core check | 2,895 n15 graphs, zero failures | c2core mode only |
| S6 certificate | Frame checks pass; labelled levels 9,47,211,1035; 17 lowering moves from depth-three frames; escape in four moves | The recovered single certificate and the explicit move/quotient conventions |
| S6 host | Projective-plane incidence axioms pass; capped essential-cut computation returns 10 | This shows minimum essential cut at least 10 under the supplied algorithm; the printed uniqueness statement is background mathematics, not checked by the program |

The S6 correction means that no lowering move exists at depths zero through two; some depth-three frames do have lowering moves. The six T2 exceptions and complete row comparison are in `replay/t2-comparison.json`. These are corrections of false historical claims, not new all-sizes results. BM/BM-2 and the n16 coverage condition remain unresolved here.

## Replay entrypoints

Use a Python environment with networkx and python-sat, a C compiler, and GNU timeout. Run from the supplement root. Compile `rpair.c`, `mpair_fixed.c`, and `papers/qb5/code/petal.c` with `cc -O2` into a separate writable build directory. Use that directory for the executable paths below. Run the built petal executable once on each file in papers/qb5/original-inputs/ via standard input. The gen585 build additionally requires the external nauty source distribution; this replay used nauty 2.8.9. Set ERDOS585_GEN585 to the built executable and ERDOS585_NAUTY_DIR to the nauty directory for level validation. The validation modules default to the bundled copies.

```
timeout 240 python3 papers/pairs/review/code/validate_rpair.py <RPAIR_EXECUTABLE>
timeout 240 <RPAIR_EXECUTABLE> r < papers/pairs/review/code/t2_Xv.txt
timeout 240 python3 papers/pairs/review/code/t2_witness.py census/pairs-lane/data/t2_none.txt
timeout 240 <MPAIR_FIXED_EXECUTABLE> < papers/pairs/review/code/mpair_bugtest_in.txt
timeout 240 python3 census/programs/gen585/test_pair.py 600
timeout 240 python3 census/programs/gen585/validate_levels.py --N 13 --EF 35 --SP 5 --SPMIN 2 --MINDF 4 --level 8 --emin 14 --emax 19
timeout 240 python3 census/programs/gen585/validate_finals.py replay/k5-control.txt 10 4
timeout 240 python3 census/programs/gen585/validate_finals.py replay/k4-control.txt 6 3
timeout 240 python3 papers/qb5/code/verify_certs.py c2core < papers/qb5/original-inputs/qb5_n15_7_8.g6
timeout 240 python3 papers/s6/review/code/variants.py papers/s6/data/pg25_depth4.json
timeout 240 python3 papers/s6/review/code/cert.py papers/s6/data/pg25_depth4.json skip 4
timeout 240 python3 papers/s6/review/code/pg_e10.py papers/s6/data/pg25_depth4.json
```

Executable placeholders require actual locally built paths. Historical broad driver scripts retain their original run sizes and are not an instruction to repeat an unbounded census. The historical programs expect well-formed graph inputs within their documented size bounds; malformed-input hardening was not part of these finite replays.

## Editorial revision checks

The subsequent wording revision changes comments, docstrings and historical role descriptions. The N4 diagnostic label now says supplementary claim; its predicate is unchanged. Noncomment C bytes and executable shell lines were compared, and Python ASTs were compared after excluding docstrings and normalizing that one label. Changed code passed syntax checks with required header context. Fresh rpair controls again checked 407 cases with zero mismatches; the 18 marked-pair bug controls again returned NONE. A bounded chain-instance check exercised the revised diagnostic label with zero failures. The large T2 enumeration was not repeated because its executable code and input bytes did not change.
