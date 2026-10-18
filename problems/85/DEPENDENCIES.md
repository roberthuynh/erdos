# Proof dependencies and provenance

The complete proof is [PROOF.md](PROOF.md). The Lean proof uses the pinned toolchain and dependency revisions in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`, including mathlib and formal-conjectures. The 64 proof files reproduce the exact accepted formalization, with an additional aggregate import module.

## Facts used

- Finite-field addition and multiplication, additive subgroup/kernel counting, and the characterization F_(p^u) ↪ F_(p^v) iff u divides v (used for the incompatible-field corollary).
- Canonical projective-space point/hyperplane counts, projective frame normalization, transitivity of PGL on frames and flags, and elementary linear algebra over a subfield and its extension.
- The point–hyperplane symmetric-design identity AAᵀ=q^(n−1)Id+λJ, derived from the counts; Cauchy–Schwarz, the union bound and Markov's inequality.

The weighted plane lemma, additive/Pexider correction, all-slope field argument, chart transport, coherence, infinity bounds and paired gap are proved in the text. No earlier audit is a theorem input. No exact-lineation representation theorem is needed as an external black box in this proof.

## Historical own-work lineage

The frozen 16 October 2026 proof has SHA256 `c610bff7713e65d336ee8a0bcda2b306d831de46b45d0fc1c346d45acfa531e4`. Its mathematical §§1–9 are retained here; the introductory and provenance text has been adapted for this edition.

The author consulted earlier own-work proofs for protected plane coordinates and additive correction. Their hashes were `230393c77aae6384e3aab58d6d563fdb6b5391e72104c3661e412c913eb169f6` and `3a7be904bb76cb92c486868f0d7f9f278bde3fd75e2c5ca0e18b4aa71a077fce`. Their necessary forms are reproduced here. They are historical predecessors, not missing dependency files. Classical antecedents are credited in [SOURCES.md](SOURCES.md).

## Licensing and exclusions

The proof and exposition are provided under the collection's Apache-2.0 license. External papers are cited, not redistributed. See [NOTICE](NOTICE). This provenance does not establish public priority.
