# Erdős 643: coefficient-one formal proof package

The finite upper-bound declaration is `Erdos643R3.CoefficientOneFinal.coefficient_one`.
For every finite vertex type, it bounds the number of edges of a 3-uniform
hypergraph by the number of vertex pairs when the hypergraph has no four
distinct edges forming two disjoint pairs with equal union. The final module
also states the shadow-plus-co-link inequality, upper bounds for the imported
upstream extremal number and forcing threshold, star lower bounds and the
resulting asymptotic equivalences. The expanded declarations
`Erdos643Design.HananiExistence.exists_design`,
`Erdos643R3.CoefficientOneHanani.extremal_eq` and
`Erdos643R3.CoefficientOneFullSolution.forcing_eq` state unconditional design
existence and exact extremal/forcing equality for all natural orders congruent
to 1 or 5 modulo 20. On successful completion, the strict check below verifies these exact
declarations and their full import closure. Its receipt records the exact sources,
checker inputs, dependency identities and accepted axioms.

This combined GPLv3 proof package contains 126 mathematical source modules.
Its final target is `Openmath.Erdos643R3.CoefficientOneFullSolution`, whose local
import closure includes all 126 sources, including the unchanged verified
69-module coefficient-one source set and 57 new design modules.
There are 23 exact declaration/defining-module/axiom probes.
The original Apache file notices and LICENSE.upstream remain intact; see
NOTICE-DESIGN.md, COPYING and licenses/Sage-COPYING.txt for derived finite-table
provenance and the combined-package licensing terms.

`source-transformations.json` records original and exported hashes. The earlier coefficient-one
source-copy changes affect comments only. design-source-provenance.json records
new import relocations and the two finite-certificate resource-wrapper removals;
the resource ceilings are supplied explicitly by the hashed design-scope.json. This does not transfer an original
source's verification result to an edited copy: a final receipt must bind these
exact exported bytes. Successful finalization writes the resulting receipt to
receipts/final-receipt.json in the local project.

## Dependency setup

Install Python 3.11 or later, Git and elan. From the package directory, elan
selects the exact version recorded in `lean-toolchain`: Lean 4.33.1.
`lake-manifest.json` pins Mathlib and all eight transitive package revisions.
The following command obtains the pinned dependencies and official Mathlib
cache into this package's own `.lake/packages` directory. Do not run `lake update`.

```sh
cd <PACKAGE_DIRECTORY>
python3 tools/setup.py
```

Setup is bounded to 240 seconds and reports UNKNOWN on timeout, terminating
its owned process group including download/build descendants. Both wrappers also
terminate remaining descendants after ordinary success or failure, preserving
the command's actual exit code. A successful
setup command does not certify a theorem or establish binary provenance.
Cold installation requires network access to the pinned upstream repositories
and official cache; the strict verifier separately checks the resulting identities.
Ordinary compilation may use another supported Lean platform, but the official
strict check below requires the supplied binary identities.

## Strict final check

The shipped `pins/toolchain.sha256` records the official Lean 4.33.1
`darwin_aarch64` installation used for the original checks. The package artifact
pins record the accepted Mathlib cache for the pinned dependency revisions.
They are platform-specific binary identities, not portable build recipes.
The strict verifier rejects any missing, additional or changed pinned artifact.
Another platform or independently rebuilt dependencies require a separately
reviewed trust base; generating replacement pins locally does not establish it.
See `TRUST-BASE.md`.

By default the verifier resolves elan's selected `lean` from PATH using
`lean --print-prefix`, then checks the actual executable, version and pins.
An explicit `ERDOS643_TOOLCHAIN` may name a toolchain root with `bin/lean` and
`bin/leanchecker`. Dependencies default to this package's `.lake/packages`.
An explicit `ERDOS643_PACKAGES` may name another dependency directory; exact
Git revisions, tracked cleanliness, module shadowing and binary pins still apply.
Set overrides identically for every phase. No sibling repository is discovered.

Run each phase separately in order; each command has an outer 240-second cap:

```sh
cd <PACKAGE_DIRECTORY>
python3 tools/run_phase.py prepare
python3 tools/run_phase.py build 0
```

Continue build chunks 1 through 125, each with `python3 tools/run_phase.py build N`.
Then run hygiene, followed by kernel chunks 0 through 125, each as its own command:

```sh
cd <PACKAGE_DIRECTORY>
python3 tools/run_phase.py hygiene
python3 tools/run_phase.py kernel 0
```

After kernel chunk 125 completes, finalize:

```sh
cd <PACKAGE_DIRECTORY>
python3 tools/run_phase.py finalize
```

Only finalization may emit `RESULT: PASS` and create
`receipts/final-receipt.json`. A timeout is UNKNOWN. Failed or timed-out phases
invalidate prior success. The checker freezes exact sources/tools/configuration,
checks all package revisions and binary pins, builds the import closure from
fresh source copies with kernel checking enabled, performs source and environment
hygiene, checks declaration ownership and allowed axioms, independently replays
every closure module with `leanchecker`, and rechecks state and binary pins.
The only allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.

Self-contained controls test stale-result invalidation, timeout classification,
startup-acknowledged descendant termination after timeout, failure and success for both wrappers,
phase order and forbidden-source rejection without running the proof:

```sh
cd <PACKAGE_DIRECTORY>
python3 -B tools/test_failure_control.py
```

`PASS_CONTROLS_ONLY` describes those controls, not mathematical verification.
The older endpoint/upstream/conditional-assembly entry points in
`tools/verify_endpoint.py` verify only their named subsets and are not substitutes
for the full phased check.

## Finite certificate update

The finite certificate in `Prime281.lean` counts witnesses within each base block and sums the counts. A kernel-checked disjointness argument identifies this sum with the original witness count. The base blocks, public theorem statements and hypotheses are unchanged. Historical receipts retain their original source identities; the full check must rebuild and replay the updated source. Its finalization writes a separate source-bound `receipts/final-receipt.json`. The required GitHub Actions full-package job executes this same procedure for the exact commit; a historical receipt is never substituted for that check.

## Upstream sources and license

The three files under `FormalConjecturesForMathlib` are unchanged copies from
`google-deepmind/formal-conjectures` commit
`95b199bfbc08f7b1183196bab59ed3b08f27c2c9`.
`upstream-source-manifest.json` pins their identities and the unchanged Apache
2.0 license in `LICENSE.upstream`. Source copyright and attribution notices
are retained. `FCBridge.lean` separately reconstructs upstream definitions in
a distinct namespace; the final extremal statements use the imported definitions.
