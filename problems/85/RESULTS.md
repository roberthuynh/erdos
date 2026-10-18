# Result index

## R1: rank-controlled point–hyperplane repair

**Full repair theorem, dichotomy and no-field-embedding bound verified in Lean; no human mathematical review.** The exact statement and all hypotheses appear in [PROOF.md §1](PROOF.md#1-the-candidate-theorem). The maps are arbitrary fixed functions between supplied PG(n,q) and PG(n,r), n≥2, q,r prime powers. With original flag error δ=T/(Nd) and ordered-frame survival ρ, the assumptions ρ>0 and δ≤ρ/(10^9 n²) imply a single coupled field-semilinear embedding with total source-entry distance D≤5T/q^(n−1)≤10T/d. The target hyperplane is the target-field span, not just the set of embedded source points.

Proof closure: §2 weighted plane correction; §§3–5 protected-frame transport and unconditional selection; §6 field coherence and global affine reconstruction; §§7–8 infinity accounting and paired design gap. Elementary facts are listed in [DEPENDENCIES.md](DEPENDENCIES.md).

## Consequences of R1

The dichotomy and no-field-embedding consequence have formal declarations listed in [VERIFICATION.md](VERIFICATION.md); they are not additional contribution families.

1. Every pair has at least one alternative: D(G)≤10T/d for some coupled embedding G, or ρ≤10^9 n²δ. Indeed, failure of the second alternative supplies R1's hypotheses.
2. **Written consequence of R1, not a separately checked Lean declaration.** Under R1's hypotheses, a frame avoiding all changed point entries survives. Each frame coordinate is uniform on the N source points, so the union bound gives 1−ρ≤(n+2)D/N≤10(n+2)δ. Thus every pair satisfies ρ≤10^9 n²δ or ρ≥1−10(n+2)δ. The alternatives need not be disjoint.
3. **Formal no-field-embedding bound; the numerical field criterion is its classical finite-field interpretation.** If the finite fields have different characteristics, or q=p^u, r=p^v with u not dividing v, no field embedding exists. Every input then satisfies ρ≤10^9 n²δ.

## Original problem and exclusions

Eventual monotonicity of the four-cycle minimum-degree threshold remains open. No f(49) determination, new extremal bound, efficient decoder, general-building theorem, sharp threshold, human endorsement or public priority claim is made. No older formal result is evidence of Lean verification of R1.
