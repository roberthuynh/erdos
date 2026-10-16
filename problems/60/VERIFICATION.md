# Verification of the stated #60 results

[Overview](README.md) · [Result index](RESULTS.md) · [Sources](SOURCES.md)

On October 16, 2026, the portable package completed its verification at the collection paths: 82 configured module builds, exact type and axiom checks for 519 registered declarations, six main-theorem oracles reporting `RESULT: PASS`, and kernel replay of all 82 modules. The module count includes 81 proof modules and the aggregate `Erdos60` root. Declaration counts include supporting results, not 519 independent mathematical discoveries.

The completed run resumed after an aggregate timeout. It retained 130 completed successful checks and ran the remaining 44 checks against the same frozen source, registry, checker and dependency identities. It was not a single uninterrupted run, and the timed-out attempt itself was not counted as PASS. Each individual Lean command was bounded at 240 seconds. Pinned dependency caches were available; this was not a cold online dependency-fetch test.

The proofs use no `sorry`, `native_decide` or custom axioms. Only `propext`, `Classical.choice` and `Quot.sound` are permitted in the audited axiom closures. Separate AI reviews checked the exact statements and source attribution. This is not human mathematical review or novelty clearance.

## Main declarations

All declarations below are in namespace `Erdos60.Headline`.

| Module | Declaration | Scope |
|---|---|---|
| [FirstExcessHeadline](FirstExcessHeadline.lean) | `first_excess_structural` | Actual same-vertex polarity and exact edit bounds in the stated real-T interval. |
| [LinearRangeHeadline](LinearRangeHeadline.lean) | `linear_range_lower` | Universal even-order M+t lower bound. |
| [EqualityHeadline](EqualityHeadline.lean) | `linear_range_equality_iff` | Matching equality classification in the same even-order interval. |
| [ExtremalHeadline](ExtremalHeadline.lean) | `power_two_extremal_and_supersaturation` | Combined exact ex/h conclusion at powers of two. |
| [ExtremalHeadline](ExtremalHeadline.lean) | `power_two_c4Extremal` | Exact extremal threshold at powers of two. |
| [ExtremalHeadline](ExtremalHeadline.lean) | `power_two_c4Supersaturation` | Exact h value at powers of two. |

The exact hypotheses remain in the [theorem statement](LINEAR-RANGE-THEOREM.md) and [result index](RESULTS.md). The results do not assert ex=M or plane existence at arbitrary even orders, nor solve unrestricted Erdős #60.

## Reproduce

The package pins Lean `leanprover/lean4:v4.33.1` and mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. From the collection root:

```bash
python3 scripts/check.py --problem 60 --mode docs
python3 scripts/check.py --problem 60 --mode full
```

Full mode builds the registered package, checks the frozen source identities and printed declaration types/axioms, runs the six oracles, and replays every configured module. Keep the command logs and receipt. A timeout remains UNKNOWN.

For one declaration, from `problems/60/`:

```bash
./check.sh LinearRangeHeadline.lean Erdos60.Headline.linear_range_lower
python3 -B scripts/replay_modules.py --module LinearRangeHeadline
```

The oracle and replay are separate checks; a single oracle PASS is not a complete-package replay. The exact module/source inventory is in `scripts/proof-modules.json`, and the 519 printed type registrations are in `scripts/headline-theorems.json`. Changes to these frozen files require renewed verification.
