# Verification

The package pins Lean in [lean-toolchain](lean-toolchain), direct dependencies in [lakefile.toml](lakefile.toml), and exact dependency revisions in [lake-manifest.json](lake-manifest.json). Use Python 3, the Lean toolchain installed through elan, and a `timeout` executable. The Lean sources are the formal statements; the manuscript provides a working exposition.

The [accepted mathematical input record](verification/accepted-mathematical-inputs.json) identifies the five headline declarations, all 103 local modules, their registered types and axiom closures, pinned dependencies and accepted evidence. Authentication of that evidence and agreement of mathematical inputs permit reuse. A binding match alone does not authenticate evidence or prove a theorem. The [collection guide](../../docs/verification.md) explains reuse and full reproduction.

From this package directory, initialize the pinned dependencies and build:

```sh
lake exe cache get
lake build
```

Check each main declaration:

```sh
./check.sh Erdos1017/SharpAffine.lean Erdos1017.sharp_affine
./check.sh Erdos1017/MesoscopicLower.lean Erdos1017.Mesoscopic.finite_lower_bound
./check.sh Erdos1017/BinomialSharp.lean Erdos1017.Binomial.exact_fractional_extremum
./check.sh Erdos1017/SlopeBarrier.lean Erdos1017.sharp_affine_slope_barrier
./check.sh Erdos1017/NearComplete.lean Erdos1017.Dense.near_complete
```

A successful theorem check prints `RESULT: PASS`. A timeout is unknown. The default invocation checks the density-dependent upper bound only.

The complete verification additionally checks source coverage, every local module's kernel replay, the declaration types and their axiom closures, and document identities:

```sh
python3 -B scripts/source_modules.py
python3 -B scripts/replay_modules.py
python3 -B scripts/check_axioms.py
python3 -B scripts/check_docs.py
python3 -B -m unittest discover -s scripts -p 'test_*.py'
```

Every Lean invocation in these scripts has a 240-second limit. The full declaration inventory must match its recorded types, source hashes and dependency pins. The only permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. The source scan rejects proof placeholders, native proof shortcuts, untrusted declarations and disabled kernel checking. No document check substitutes for a theorem check or kernel replay.

The source reviews used for the five statements examined their exact hypotheses, original graph edges, costs, support and quantifiers. They were conducted by AI systems; no human mathematical review or different-model independence is claimed. Mathematical correctness of the formal statements, agreement of the exposition with those statements, and historical priority are separate questions.

The manuscript is a working draft. Its compilation checks typesetting only. Integral asymptotic statements that require an external rounding theorem are outside this package's five formal conclusions.
