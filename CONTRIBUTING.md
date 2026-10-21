# Contributing

Corrections, mathematical review, prior-work references and reproducibility reports are welcome. Identify the problem number, exact claim or declaration, source path and version. For a suspected error, give a counterexample or the proof step that fails. For prior work, link a public source and explain which hypotheses and conclusion coincide.

Review written proof correctness, formal-statement fidelity, computation coverage, kernel verification and novelty separately. Explain what you inspected and what remains unchecked. A successful build cannot resolve a mismatch between prose and a Lean statement.

Before changing a problem package, read its README, RESULTS and verification instructions. Preserve exact hypotheses, pinned dependencies, notices and historical receipts. Avoid mixing a proof change with a directory move or dependency upgrade. New packages follow [the admission guide](docs/adding-a-problem.md).

Run the applicable [checks](docs/verification.md), and report the command, environment, outcome and any timeout. Changes to shared checks require validation of affected package coverage. Reuse authenticated complete Lean evidence for unchanged mathematical inputs; verify changed proofs and their affected dependent scope. Do not include confidential drafts, private exchanges, credentials or unlicensed copies of papers. Public source citations are preferred to redistributing third-party material.

AI assistance is permitted and should be described accurately. Name the evidence and review actually obtained; do not imply human review or novelty from an AI review. Public wording and release decisions require maintainer approval.
