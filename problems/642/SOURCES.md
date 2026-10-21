# Sources and attribution

## Problem and prior bounds

- [Erdős problem #642](https://www.erdosproblems.com/642) asks whether sufficiently large constant average degree forces a cycle with at least as many chords as vertices. This package proves a cubic-logarithmic sufficient average degree, not the constant-degree conjecture.
- Nemanja Draganić, Abhishek Methuku, David Munhá Correia and Benny Sudakov, *Cycles with many chords*, Random Structures & Algorithms 65 (2024), 3–16, [DOI 10.1002/rsa.21207](https://doi.org/10.1002/rsa.21207), [arXiv:2306.09157](https://arxiv.org/abs/2306.09157). Their theorem gives the same chord conclusion from an eighth-power logarithmic density threshold.
- Nemanja Draganić, *New tools for sparse graph embeddings: Hybrid expanders and application to nested cycles*, [arXiv:2610.16572v1](https://arxiv.org/html/2610.16572v1), 12 October 2026, introduction. This preprint announces upcoming work reducing the required average degree for the same chord problem to essentially order $\log\log n$. That announced scale is stronger than the cubic-logarithmic bound here. The announcement itself is not a full proof of that result. We do not claim that our bound is currently best or that it has priority over the announced work.

## Methods

- Micha Christoph, Zach Hunter and Benny Sudakov, *Thinning and sprinkling: from robust sampling to almost Hamiltonicity*, [arXiv:2609.30165v1](https://arxiv.org/html/2609.30165v1), 24 September 2026. The sampling and tough-layer methods inform this construction. Section 8 develops path merging and almost-spanning cycle arguments. The formal development proves its own required interfaces; it does not assume the paper's conclusions as axioms.
- Debsoumya Chakraborti, Oliver Janzer, Abhishek Methuku and Richard Montgomery, *Edge-disjoint cycles with the same vertex set*, Advances in Mathematics 469 (2025), 110228, [DOI 10.1016/j.aim.2025.110228](https://doi.org/10.1016/j.aim.2025.110228). Regularization and extraction ideas from this line of work are used in the earlier host construction.

## Scope of the comparison

The primary-source comparison concerns the exact conclusion: one simple cycle with at least its own length in distinct chords. Results allowing a loss in the number of chords have a different conclusion. The comparison distinguishes published theorems, preprints and announcements. It does not establish that every ingredient or supporting lemma is new. No claim about inaccessible or unpublished proofs is made.

The October 2026 preprints above were consulted at the linked versions. Later work can supersede the comparison. The result and formal statement remain valid independently of a priority assessment.

## Attribution and licenses

AI systems developed the arguments and Lean proofs and performed the source reviews. Robert Huynh directed the work. No human mathematical review is claimed. The manuscript has one named author and separately discloses AI use.

Lean, Mathlib and the formal-conjectures dependency retain their own licenses. The package does not include copies of the cited papers. [NOTICE](NOTICE) records the source attribution and [CITATION.cff](CITATION.cff) describes how to cite this package.
