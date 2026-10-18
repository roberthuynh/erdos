# What the repair theorem says

The input is a pair of proposed incidence maps. Most source flags may be correct even when every point has collapsed into a low-dimensional target subspace. The theorem requires a measurable population condition, frame survival, that rules out that failure when it exceeds the specified error scale. It then repairs both maps to one field-semilinear embedding.

## Why frame survival matters

For n≥3 and a sufficiently large target field, put all source point images on one target line W and all hyperplane images among hyperplanes containing W. Both functions can even be injective when the target supplies enough choices. Every flag is preserved, so T=0, but no full frame survives: ρ=0. Small individual fibers cannot detect this collapse. The theorem deliberately excludes it through ρ>0 and the quantitative comparison with δ.

## The proof mechanism

Transport pays for errors that would otherwise make restriction to a plane invalid. Coherence prevents different plane corrections from choosing incompatible field maps.

1. Protect a surviving frame and its coordinate data using at most 7n² original flag slots.
2. Restrict to coordinate planes only after charging point-membership and complementary-span failures. Each induced flag has a pointwise majorant of 2n−3 original flag errors.
3. Use 24 weighted flag families to pay for diagonals, reciprocal witnesses and protected rows. Their costs are averaged before conditioning on frame survival.
4. Compare all corrected scalar maps to the same original coordinate pencil, including default inputs. Agreement on more than half the field forces one field embedding.
5. Recover the whole affine chart from all n coordinate pencils. Count infinity errors and use the source symmetric-design gap to repair both maps with D≤5T/q^(n−1).

The plane correction, additive correction and spectral-design identities are ingredients and antecedents. The higher-rank transport and consistency interface is the package's focus. This is a description of the argument, not a claim that the mechanism has established public priority.

## A scale check

Start with an exact embedding, move one source point to the embedded image of another source point, and leave the hyperplane map unchanged. Exactly q^(n−1) source flags break, while only one entry changed. This illustrates the source-degree normalization. It is not a sharpness proof for the theorem's constant or frame threshold; the small-error hypothesis must still be checked for any chosen parameters.

## Limits

The frame/error threshold may require very large spaces before nonzero integer errors are admitted. The result supplies existence, not an implemented or efficient decoder. The corollaries in [RESULTS.md](RESULTS.md) reuse the same theorem. Earlier graph reductions, cubic-root repair and coloring applications are not claimed or verified by this package.
