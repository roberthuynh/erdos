# Decisions

Robert Huynh · October 11, 2026

This page lists the calls I made while steering AI agents on Erdős 585 between September 29 and
October 11, 2026: what I accepted, what I rejected or stopped, what I changed, and which check caught
each mistake. The dated log the agents kept for me is private; this is its digest, written from the
project's own records. A clean build, a passing CI run or a finished pipeline is not evidence that a
result is right. The checks named below are what I relied on instead.

## Rules I set, and why

1. I accept a Lean proof only after the check script reports that the file builds, has no `sorry`, and uses only
   the three standard axioms. Proofs by `native_decide` do not count. Why: the first things the
   agents produced that looked finished were not.
2. Four judgments are kept separate and recorded separately: whether a Lean statement says what the
   written statement says, whether the written proof holds, whether the kernel accepted the Lean
   proof, and whether the result is new. Why: I once read a helper lemma's kernel receipt as the
   main theorem's, and a passing check of the wrong statement is worth nothing.
3. Nothing is called new until a specialist says so. The public wording is "no earlier statement
   found so far". Why: the end of the first attempt said "none of this is in the literature", which
   only meant that the agents' search had found nothing.
4. A finite search counts as evidence only after a calibration shows where known examples first
   appear. Why: "no degree-6 example through 14 vertices" was read as support before anyone measured
   that the known degree-5 examples start at 18 vertices, with earlier records at 32 and 104.
5. Every main written claim gets a separate AI reviewer in a fresh context, with its own code,
   before Lean. The reviewed file is frozen by hash. Why: shared context can carry the author's
   assumptions into the review.
6. Every agent writes its state to disk every few minutes. Why: runs were paused twice on usage
   limits and resumed from files; nothing was lost.

## Attempt 1, September 29 to October 1: choosing the problem

- Accepted: 585, because it was quiet, precise and had no formal statement upstream. Rejected: every
  candidate that looked approachable; each already had recent claims or forum results. Checked by:
  a join of the public open-problems tracker, the formal-conjectures list and a challenge catalog.
- Rejected: an automated tactic sweep over 43 open statements. It closed none and was not continued.
- Changed: the first Lean statement. It built cleanly with the answer function quantified in the
  wrong order. Caught by a maintainer-style review before submission. A clean build is not evidence
  that a statement is right.
- Rejected: the sentence "None of this is in the literature." Rule 3 came from this.

## Attempt 2, October 1 to 4: scale

- Accepted: the finite results and constructions, each checked two ways: f(6) and f(7) in Lean, the
  values f(11) and f(12), and 5-regular graphs with no pair on 32 and 104 vertices.
- Stopped: an evolutionary search for degree-6 examples, after its positive control timed out and
  it tied plain random search in a separate comparison at the same compute. Rule since then: before scaling a search, require a
  graded score, an independent exact check, a held-out test and a matched-compute random baseline.
- Changed: the goal text. "Prove something each round" was met with easy special cases, and one
  agent declared the goal done at its lowest tier and stopped. Since then the goal text holds the
  target, the ladder of what counts, one line saying what does not count, and the hard rules.
  Progress is tied to the hard case. Caught by reading the run, not by any check.
- Changed: how "none found" is read (rule 4). The calibration was done in attempt 3.
- What I took from it: the pass count, the helper results and the barriers all grew without moving
  the target. More agents measured activity, not progress.

## Attempt 3, October 4 to 6: one bet, every claim through a gate

- Accepted: one question, about bipartite graphs with maximum degree 6, where a computer can decide
  the small cases and either answer is a result. The attempt was limited to it.
- Changed: the order of checks. The lead agent checks a claim by hand, a separate reviewer
  re-derives it with its own code, the reviewed file is frozen, and Lean comes last. The first
  theorem went from the start of the attempt to a passing Lean check in about 12 hours; the stronger
  one took 17 Lean files.
- Changed: a review I had requested on one model ran on another, and only the transcript showed it.
  The account was corrected, and a later review did run on the model named. A "different model
  checked it" claim has to be read from the logs.
- Changed: statement fidelity got its own check. A fresh reader compared each Lean statement with the
  written one.
- Accepted with fixes: claims the AI reviewers sent back. Section 7 of the findings says how each
  written proof was reviewed. AI review earns its keep on exact hypotheses, constants and counts; it
  is not human review.
- Open after it: the degree-6 pair question itself. The theorems rule out one way a counterexample
  could be built; they say nothing about pairs.

## Attempt 4, October 7 to 11: exact targets

- Accepted: exact targets with fast checks, thresholds and constructions whose small cases can be
  decided exactly. Data first, then a conjectured constant, then a frozen statement, then a proof
  attempt. Minutes after the first fitted formula was frozen, the gate turned up an accepted
  construction that contradicted it. That is the loop working.
- Changed: every agent finish is graded on a scale anchored to published results, with an hourly
  tally. A sharp threshold at a fixed small degree stays at the same level however sharp it gets.
- Stopped: one census route, on October 7, rather than buy 1,600 to 2,100 core-hours.
- Stopped: the open-ended structural hunts on the main question. They produced refutations, 16 on one
  program, and no theorem. Three rounds of proposals gave 38 candidates and none passed the gate
  clean.
- Rationed: most of the volume ran on GPT-6.1 Sol; GPT-6 Astra was capped at two workers at a time.
- Changed: my steering messages. Eight of twenty began "Additive:" and added a priority without
  rewriting the goal.
- Caught: a reframing the lead agent proposed as new was already in attempt 2's files. Ideas are now
  gated against the project's own archive as well as the literature.
- Accepted: the generalization from fixed thresholds to one theorem for every parameter, with its
  cutoff lowered twice.

## Before release: what a second verification caught

A separate set of agents rebuilt the tree, reran every check and read the public files without
access to the private record. They found 44 issues. The ones that changed the release:

- 41 Lean files carried another project's copyright line. Fixed.
- The README's build command had a timeout that cannot finish on a fresh clone, and the CI job was
  projected over its limit. Fixed: the limit is now 150 minutes, and a fresh run of the exported
  tree took about 48 minutes at 2 threads.
- The headline understated the result: the parameterized theorem beats the stated corollary at every
  q from 2^18 on, by a factor between 1.5 and 2. The general theorem now leads.
- The release text said the AI "assisted"; the README says it produced the work. One verb now.
- A comparison with a published remark was stated for general graphs; it holds for bipartite graphs.
  Fixed.
- A credit the previous version carried had been dropped. Restored.
- The verification claim was repeated in six files with no transcript behind it. One dated paragraph
  now, with the transcript in the supplement.

Decisions I took on their findings: keep my introduction as it was; keep the note that the upstream
pull request is still under review, which it is; restore the credit; lead with the general theorem.
