# Verification of the stated #642 result

[Overview](README.md) · [Result index](RESULTS.md) · [Sources](SOURCES.md)

On 16 October 2026, the portable package completed the collection’s full verification gate at its release paths: all 135 configured modules built, the exact types and axiom closures of 2,163 local environment declarations matched their frozen registry, the main theorem’s official checker reported `RESULT: PASS`, and all 135 modules passed kernel replay. The module count includes 134 proof sources and the aggregate `Openmath` root. Declaration counts include definitions, supporting results and compiler-generated constants; they are not a count of independent discoveries.

The run completed through bounded continuations after aggregate timeouts. Successful commands were retained only when their exact command, relevant source/pin/checker identities and log hashes matched. Builds depend on the frozen mathematical source and pins; audits and replays also depend on their verifier scripts. An auxiliary timeout-reporting correction required affected checker phases to run again. The timed-out attempts were UNKNOWN, not PASS. Each Lean command was limited to 240 seconds. Pinned dependency caches were reused; this was not a cold online dependency-fetch test. The [verification summary](verification-summary.json) records final counts, identities and log digests.

The proof sources contain no `sorry`, `native_decide` or custom axiom declaration. Only `propext`, `Classical.choice` and `Quot.sound` occur in the audited axiom closures. The release checker fails if the Lean build or axiom probe fails, if the requested report is missing, or if an unexpected axiom appears. Regression controls exercise these failures. The old auxiliary linter-option diagnostic has been removed; it is not ignored in this gate.

## Exact theorem and scope

The main declaration is `Erdos642.CampaignFe72210bContinuation3.OriginalBound.original_log_five_rich_cycle` in [OriginalBound](Openmath/Erdos642/Proofs/CampaignFe72210bContinuation3/OriginalBound.lean). Its full hypotheses and interpretation appear in the [result index](RESULTS.md).

Fresh-context AI reviewers separately inspected the statement, mathematical exposition, attribution and evidence claims. Their reading scopes are limited: they did not each read every source module. These reviews are not human mathematical review or novelty clearance. Kernel replay checks formal correctness; it does not establish that the result is new or that every informal explanation is correct.

## Reproduce

Replace `<COLLECTION_CHECKOUT>` with the absolute path of a clone. From a fresh terminal:

```bash
cd <COLLECTION_CHECKOUT>
python3 scripts/check.py --problem 642 --mode docs
python3 scripts/check.py --problem 642 --mode full
```

Docs mode checks local links and the frozen source and artifact hashes. Full mode additionally runs the failure controls, builds the complete dependency closure, compares every registered type and axiom closure, runs the main-theorem oracle and replays every configured module. Look for `642 full: PASS`; a timeout remains UNKNOWN. Keep the receipt and command logs. The collection’s CI uses these same registered checks; hosted CI results are recorded on the release pull request, separately from these local verification receipts.

The package pins Lean `leanprover/lean4:v4.33.1`, mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and formal-conjectures `137aec5c7abd3aa61f7a73138a97279acfc79e93`. A cold machine may need dependency downloads and multiple bounded build attempts. No network install success is claimed here.

For the headline alone:

```bash
cd <COLLECTION_CHECKOUT>/problems/642
timeout 240 bash check.sh Openmath/Erdos642/Proofs/CampaignFe72210bContinuation3/OriginalBound.lean Erdos642.CampaignFe72210bContinuation3.OriginalBound.original_log_five_rich_cycle
```

Look for `RESULT: PASS`. This single oracle is not the complete-package gate. The [module inventory](scripts/proof-modules.json), [declaration registry](scripts/headline-theorems.json) and [source identities](source-identity.json) bind the verified package. Changes to a proof, dependency pin or checker require renewed applicable checks.
