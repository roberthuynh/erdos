# Adding a problem

The catalogue contains #60 and #585. The numbered package boundary can accommodate future work on #85, #642 or #643; naming them here makes no claim about unpublished results, readiness or verification. Do not create empty result directories as placeholders.

A released package lives at `problems/<number>/`. Use the same README section order for every problem: **The problem**, **Main results**, **Status**, **Prior work**, **Proofs and findings**, **AI use**, **Verification**, and **Citation and corrections**. Begin with the question and a short explanation of its terms. Give exact hypotheses and an explicit evidence description beside each main result: Lean-checked theorem, computational result, or AI-reviewed written candidate. Put the relation to the original problem and review state under Status. A later status paragraph must not be the first indication that an earlier claim is unproved or unformalized. Preserve meaningful result-specific subsections rather than copying irrelevant Lean or census sections into every package. Keep first-person prose on the collection homepage; link to it from a short, problem-specific AI disclosure. Use factual, impersonal language for mathematical summaries and verification records. Do not invent first-person narrative. Place build details under Verification and repository-layout notes in the migration guide. RESULTS indexes exact claims and their proof or check records. Keep a problem-specific citation and any required notices. Formalized packages retain their own pinned Lake environment; different packages need not share a compiler pin.

Before admission:

1. Freeze exact statements, hypotheses and quantitative ranges. Distinguish the original problem from partial results and conditional statements.
2. Include the licensed proof dependency closure and retain source provenance. Exclude credentials, confidential materials and unlicensed paper copies.
3. Compare relevant eligible public sources freshly and record versions, exact theorem differences and reading limits. Preserve unresolved priority questions.
4. Review proof correctness and statement fidelity independently. For computations, specify coverage and replication. For Lean claims, obtain the applicable official `RESULT: PASS`, inspect axioms and check the formal statement against the written claim.
5. Register only the released package in the collection catalogue and its applicable checks. Run metadata, links, export-boundary and package verification at final paths. A prose-only package must not imply that another package’s Lean checks verify its mathematics.
6. Obtain maintainer approval of public wording and the separate authorization for publication. Preserve historical evidence and the exact release state.

Changes to shared verification logic must run every affected package. Avoid moving mathematical claims into the root catalogue: the package is authoritative for their scope and evidence.
