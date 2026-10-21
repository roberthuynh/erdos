# Erdős Problem 643

[Collection](../../README.md) · [Results](RESULTS.md) · [Proof](SOLUTION.md) · [Evidence](EVIDENCE-LEDGER.md)

## The problem

A finite simple 3-uniform hypergraph H is avoiding if it has no four distinct original triples A,B,C,D with A∩B=C∩D=∅ and A∪B=C∪D. Extra triples on those six vertices are allowed. There is no linearity, codegree or additional forbidden-subgraph hypothesis.

The main theorem is

$$2|H|\leq |\partial H|+|\mathrm{CL}(H)|.$$

Here ∂H is the set of pairs contained in an edge, and CL(H) consists of pairs {x,y} having a nonempty common link: some pair P disjoint from {x,y} has both P∪{x},P∪{y} in H. Each pair set is contained in the vertex pairs; they need not be disjoint. Thus the inequality implies |H|≤binom(n,2), including n=0.

## Main results

Let ex₃(n) be the maximum avoiding size and f(n;3)=ex₃(n)+1 the minimum forcing threshold. The theorem gives f(n;3)≤binom(n,2)+1. With Füredi's classical star-plus-matching lower construction, it settles the t=3 asymptotic question f(n;3)=(1+o(1))binom(n,2). The all-order upper statement is stronger than a sufficiently-large-order conjecture. It supplies neither higher-uniformity results nor equality classification or stability.

The theorem supplies the t=3 case of the asymptotic question in Erdős Problem 643. Huang, Ma and Yang's [versioned preprint, Theorem 1.2](https://arxiv.org/html/2609.37744v1) supplies the cases of every fixed t≥4 for sufficiently large n, with an order threshold depending on t. Taken together, these results give an affirmative answer to the asymptotic question for every fixed t≥3. The higher-uniformity cases rely on that external preprint and are not Lean-verified here; the Lean verification supplied here covers our triple theorem and the stated triple design consequences. This does not determine every finite extremal value or classify all triple equality cases.

Füredi's K5-filled Steiner-system construction provides classical equality examples at its design orders; these are not the only systems with equality in the stronger shadow/co-link inequality. Equality of 2|H| with |∂H|+|CL(H)| is different from |H|=binom(n,2). The supplied [cone3/cone4 examples](examples/results.json) attain the first equality but not the second. The separate [DA2 host](examples/hosts/da2-host.json) realizes a tight local anchor-box point with activity two, while its final anchor margin stays positive.

## Status

**The finite coefficient-one bound, t=3 asymptotic result and exact residue-class values are Lean-verified. Human mathematical review remains open.** General Hanani design existence and the exact values at every natural order n≡1 or5 (mod20) are included in the [combined proof package](coefficient-one-design/README.md).

## Prior work

Pikhurko and Verstraëte proved the all-order 13/9 bound. The author's earlier public package gives 4/3. Development records for 9/8 and 24/23 concern intermediate bounds and cannot certify coefficient one; their exact export status is in [Verification](VERIFICATION.md). Mubayi's coefficient-one theorem also forbids K^(3)(1,2,4). Huang, Ma and Yang treat fixed r≥4 for sufficiently large n, separately from this r=3 argument. [Sources](SOURCES.md) gives versions and limits without a priority claim.

## Proofs and findings

The [written proof](SOLUTION.md), [expanded steps](EXPANDED-STEPS.md), [manuscript PDF](manuscript/main.pdf) and [TeX sources](manuscript/main.tex) explain the slot/profile reduction, deficient-triple structure, active bicones and proportional redistribution. Source-level transcription review, mathematical review, certificate execution and page-layout inspection have different scopes. No acceptance of changing files is inferred from an older review.

The [certificate specification](CERTIFICATES.md) identifies the required thresholds, full finite domains, target-equality vectors and arithmetic methods. [Computations](computations/README.md) contains actual sources and outputs. Optional larger exact minima and exhaustive minimizer claims are omitted because their separate minimization evidence is not supplied. [Evidence ledger](EVIDENCE-LEDGER.md) identifies inspectable artifacts and remaining gaps.

## AI use

AI systems produced the proof, programs and proof readings under Robert Huynh's direction. Robert is responsible for this presentation; no personal mathematical verification or institutional endorsement is implied.

[Provenance](PROVENANCE.md) records the disclosed roles and source transformations.

## Verification

[Verification](VERIFICATION.md) separates the historical 4/3 theorem, intermediate formal bounds and the full target. The unconditional coefficient-one theorem and its stated consequences passed the complete check in the [combined proof package](coefficient-one-design/README.md). The older conditional endpoint alone does not establish that result. Documentation, compilation and finite tests do not establish full formal verification.

## Citation and corrections

The citation file identifies this problem package; the coefficient-one update has no published release identifier or DOI. Corrections should identify the exact statement, file and inference.
