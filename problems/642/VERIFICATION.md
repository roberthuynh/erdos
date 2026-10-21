# Verification and its limits

## Existing mathematical evidence

The cubic-logarithmic theorem has an official headline check and a clean build, source scan, kernel replay and environment axiom audit over its 256-module local import closure. Independent AI reviews accepted the exact original sources and their statement fidelity. The check completed on 24 October 2026. The allowed axioms were `propext`, `Classical.choice` and `Quot.sound`.

The earlier fourth-power and adaptive whole-graph theorems have accepted source reviews, official checks and the accepted full replay sweep of 19 October 2026. The published fifth-power theorem has its earlier portable package checks and that replay sweep. The six named supporting statements in [RESULTS.md](RESULTS.md) each have official and clean checks, with independent acceptance on 21 October 2026. Each statement keeps the precise restrictions listed there.

The portable receipt in [history/log5/verification-summary.json](history/log5/verification-summary.json) belongs to the previous fifth-power package: 134 proof sources plus its aggregate module. It does not verify the new cubic-logarithmic package.

## This package

The current package contains 263 proof modules plus `Openmath.lean`. The [accepted mathematical input record](verification/accepted-mathematical-inputs.json) binds the current mathematical sources, statements, axiom closures and pinned dependencies to accepted checks. It distinguishes the 263 proof modules from the imports-only aggregate. Public comment edits preserve executable Lean commands. Authentication of the accepted evidence and comparison of mathematical inputs allow those checks to be reused; a binding match alone does not authenticate the evidence or prove a theorem. [The collection guide](../../docs/verification.md) explains this distinction. The [verification summary](verification-summary.json) records that evidence is reused rather than newly executed.

Full reproduction runs the following operations. These commands remain available to readers; unchanged mathematical inputs do not require another proof run for a presentation-only change:

1. Building the configured modules with the pinned toolchain and dependencies.
2. Scanning every local proof source for prohibited proof shortcuts.
3. Checking every frozen declaration type and its axiom closure.
4. Replaying the kernel declarations from every local module, including all imports in the package.
5. Running the named headline checks, artifact identity checks and documentation-link checks.

`check.sh` accepts an optional source path and declaration name. Its default target is the cubic-logarithmic theorem. `scripts/check_axioms.py` checks the complete declaration registry; `scripts/replay_modules.py` replays the complete source inventory. Each Lean invocation is limited to 240 seconds. Failed or timed-out commands cannot count as a pass.

## Trust and scope

The checks use Lean's kernel and the three allowed axioms. They reuse pinned dependency artifacts where available; this is not a claim of a cold online installation or a rebuild of every dependency. Kernel replay uses Lean's own implementation, not an independently implemented kernel.

A change to mathematical inputs requires verification of the affected scope. Presentation-only transformations require source-identity and coverage checks against authenticated accepted evidence. Formal checks establish the precise declarations; they do not establish novelty. A bounded independent AI review checked this working manuscript’s headline statements, supporting hypotheses, comparison with prior work and source identity. It did not rederive every supplier proof or audit every sentence. No human mathematical review is claimed.
