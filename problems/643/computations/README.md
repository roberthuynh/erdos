# Finite arithmetic certificates

The six replay commands check finite profile inequalities, a residual anchor box and bounded host examples. They do not verify the full hypergraph theorem, its analytic reductions, or the map from arbitrary hosts to these profiles. See the separate [verification status](../VERIFICATION.md).

## Environment and commands

The recorded environment is CPython 3.14.7 and NumPy 2.5.4 on macOS arm64. `requirements.txt` pins the CPython 3.14, macOS 14+ arm64 wheel by SHA-256. No NumPy binary is redistributed here. Obtain that wheel from its distributor and put it in `<NUMPY_WHEEL_DIRECTORY>`. A different platform, Python or wheel needs a separate dependency record and replay.

Replace placeholders with absolute paths. `<PACKAGE_PATH>` is this directory; choose a new `<VENV_PATH>` and a `<RESULT_PATH>` that does not exist.

```sh
cd <PACKAGE_PATH>
python3.14 -m venv <VENV_PATH>
timeout 240 <VENV_PATH>/bin/python -I -m pip install --no-index --require-hashes --find-links <NUMPY_WHEEL_DIRECTORY> -r requirements.txt
<VENV_PATH>/bin/python -I replay.py <RESULT_PATH>
```

The runner exclusively creates the result directory, rejects any existing directory (including an empty one or one holding an older PASS), verifies `SHA256.json`, and bounds each check at 240 seconds. Look for final JSON with `"result": "PASS"` and `"checks": 6`. Stdout, stderr and actual exit codes are saved in the result directory. A timeout writes `failure.json` with UNKNOWN, command identity and partial stdout/stderr, then exits nonzero. Other checker failures, invalid JSON and hash mismatch write a FAIL receipt and exit nonzero. No failed run creates `replay.json`. An attempt to reuse a directory fails before touching its older artifacts; that older receipt belongs solely to its original run.

Use isolated Python as shown. The runner rejects `-O` and `-OO`: assertions implement checker acceptance, and optimization disables them. Isolated child interpreters ignore `PYTHONOPTIMIZE` and other Python environment overrides.

## Commands and exact boundaries

| Command | Domain and conclusion | Arithmetic and limits |
|---|---|---|
| `check_profiles.py box` | 364 triples `(tA,tB,tC)` with nonnegative entries and sum at most 11; six relation counts from 0 through 92. Threshold 23/12 for sum at most 1, and 2 otherwise. Also checks 12 position/class cases for noncompliant sum-one profiles. | Signed int64 lower enclosures at scale 2^40; near-threshold profiles are enumerated with exact `Fraction`. The reduction to this finite domain is a separate proof obligation. |
| `check_profiles.py tail` | 364 triples and three noncompliant sum-one cases. Four rest counts from 0 through 92; the negative tail correction minimizes over integers 23 through 160 together with zero. | Integer lower enclosures and exact rational checks. The written analytic tail reduction remains necessary. |
| `crosscheck_profiles.py` | Four selected type-count triples and all six counts from 0 through 4; compares min-plus elimination with exhaustive enumeration and checks enclosure against rational values. | Imports formulas and code from the primary checker. This is an implementation control, not an independent conceptual proof or full-domain independent replay. |
| `check_wbox.py` | Historical 3,401-point residual domain, including 122 points in the empty mutual variant. | Exact `Fraction`. Those 122 points are not configurations in the corrected theorem; its domain is checked separately below. |
| `c1_integer.py` | Six counts from 0 through 92, with the four type-count triples of sum at most 1; certifies a lower bound of 23/12. Includes exhaustive controls on the 0-through-3 box. | Unbounded Python integers, scale 2^32, forbidden entries represented by `None`, five min-plus products and a minimum diagonal. It gives a lower bound, not the exact rational minimum or a minimizer classification. Its author inspected the primary checker and shares the cycle reduction. |
| `check_additions.py` | Corrected 3,279-point residual box, six relabellings, a bounded rational U2 grid and compliance grid; all 1,024 hosts on five labelled vertices, all 4,845 four-edge hosts on six labelled vertices, and three specified deficient-family examples. | Exact `Fraction` and integer/set checks. Bounded examples do not prove the universal host or arbitrary-parameter statements. |

The corrected box uses `0 ≤ nB,nC ≤ 11`, `1 ≤ m+m′ ≤ 6`; positive m requires positive nB, positive m′ requires positive nC, and the zero-shore filters in the proof are imposed. Its minimum is zero only at `(1,0,1,0)`. The historical 3,401 total equals 3,279 corrected points plus 122 empty-mutual points. Their counts and equality lists are different.

In the int64 checker the largest numerator is below 2^54, every finite path is below `300·2^40`, and adding six `2^58` sentinels stays below 2^61. Exact rational checks decide the near-threshold profiles. The separate integer checker uses unbounded Python integers. No floating-point comparison decides acceptance.

All domains are generated in the scripts. There are no hidden input files, network calls, credentials or telemetry. These computations do not establish full-theorem Lean verification or human mathematical review.

The [recorded replay summary](results/summary.json) and six JSON outputs in `results/` preserve the observed counts. The replay used a fresh virtual environment and copied package on the same machine; the operating system and Python interpreter were not rebuilt. The bounded host examples observed at most one active incidence, so they do not test general multi-active anchors.

## License and source identity

The checker sources use the collection's Apache-2.0 license. NumPy remains an external dependency with its own license and bundled-component notices; its wheel is not redistributed or relicensed here. Two docstrings and one explanatory output string were adapted. The profile checker additionally records every exact target-equality vector reached by its existing inclusive enumeration; formulas, filters, loops, constants and assertions were preserved. The runner now enforces fresh output directories and structured failure reporting. `SHA256.json` identifies the exported copies, excluding itself and rebuildable caches.

## Reproducible output identities and equality vectors

Each successful runner row records `semantic_sha256`: recursively remove only JSON keys `seconds` and `elapsed_seconds`, serialize with sorted object keys, compact separators and UTF-8 (`ensure_ascii=False`), then SHA-256. List order, rational strings and every non-timing field are retained. The six reference identities are in `results/semantic-hashes.json`; this normalization identifies finite-check outputs, not the full theorem. Test normalization and failure handling with `timeout 240 <VENV_PATH>/bin/python -I test_replay.py`.

The box and tail outputs now include `target_equality_vectors`, with coordinate order, type counts, target and class or noncompliance context on each entry. They enumerate equalities at the tested targets, not larger exact auxiliary minima or their minimizers. Separate branch-and-bound sources needed to certify such larger minima are not supplied here, and no auxiliary minimum completeness claim follows from these checks. No unverified source or historical output was imported to fill that gap.

The exact original checker identities and export transformations are recorded in `source-provenance.json`. The original mathematical expressions and acceptance checks remain unchanged; output instrumentation only appends equality data. The original source hashes are provenance identifiers, not an independently published source archive.

## Bounded independently coded formula controls

The portable `independent_audit.py` and `pruning_controls.py` provide inspectable finite controls; their JSON outputs are in `results/independent_audit.json` and `results/pruning_controls.json`. Run each with `timeout 240 <VENV_PATH>/bin/python -I <PACKAGE_PATH>/independent_audit.py` and `timeout 240 <VENV_PATH>/bin/python -I <PACKAGE_PATH>/pruning_controls.py`. Both reject optimized Python.

The first compares independently coded rational formulas and feasibility predicates to both checker implementations on 5,832 small profiles, checks 49,152 class-mask memberships, all 1,248 tail parameter pairs, 5,000 bounded rest profiles, and the entire 3,279-point corrected anchor box. It also removes admissibility constraints and raises a bounded target as negative controls. The pruning control compares the actual pruning routines with direct small-domain rational enumeration, including all three sum-one positions; it slices matrices and changes only the tail domain constant for this bounded test. These controls do not independently reproduce all six full domains, certify larger auxiliary minima, validate universal host reductions, or verify the main theorem. Shared formula/code dependencies remain visible in the sources. No human review or independence of the whole proof is implied.

Actual sanitized six-command receipt: [results/replay.json](results/replay.json). Actual eight-control outcome: [results/runner-controls.json](results/runner-controls.json). Paths are portable placeholders; exit codes, checker semantic hashes and recorded environment are retained. These are computational and runner-test receipts, not theorem acceptance.
