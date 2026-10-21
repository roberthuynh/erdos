# Solving Erdős Problems with AI

Hi, I'm Robert Huynh, currently a second-year MBA student at Harvard Business School. I'm a founder and absolutely not a mathematician, but I'm excited to tackle questions from Erdős's collection of unsolved math problems.

I'm always curious to see how far I can push the limits of AI before I find failure (and trust me, I've found a lot of it)!

# Erdős #643: the sharp bound for triple systems

My biggest contribution is [Erdős #643 (manuscript)](problems/643/manuscript/main.pdf) because it resolves the final remaining case of its asymptotic question: the t = 3 case. The result gives an all-order upper bound and exact classical design-order values, checked in Lean.

The work on Erdős #643 settles its t = 3 asymptotic case, completing the remaining case of the asymptotic question together with [Huang, Ma and Yang's preprint](https://arxiv.org/html/2609.37744v1), which treats every fixed t ≥ 4 for sufficiently large n. Our triple-system result is Lean-verified; their higher-uniformity proof is external and is not Lean-verified here. Other packages, including #60, #583, #642 and #1017, give partial results on their original questions. #585 explores regular-subgraph bounds and finite cases, while #85 develops a separate projective-incidence theorem. I hope this work inspires more collaboration between mathematicians and people like me, who found their interest in math later in life and still want to contribute.

## How this was made

I pointed AI agents (from both Anthropic and OpenAI) at solving Erdős's math problems. As the agents proposed ideas, wrote proofs and search programs, and reviewed each other's work, I steered them back to the big question: could we actually change our understanding of these problems?

### 1. Get a statement we can check

I needed a way to know whether the agents' proofs were correct. So I used [Lean](https://lean-lang.org/doc/reference/latest/ValidatingProofs/), a program that checks proofs written in a precise mathematical language, and had the agents build checks around it. A `sorry` in Lean means part of the proof is missing. It does not count as a pass.

Lean checks the statement it is given. One early formal statement compiled with the quantifiers in the wrong order, changing the question it asked. I made [statement review](problems/585/findings/DECISIONS.md#rules-i-set-and-why) a separate check. The problem pages say which results have passed these checks and which are still written candidates.

I've been using [Google DeepMind's Formal Conjectures repository](https://github.com/google-deepmind/formal-conjectures) to find formal statements of open problems. For Erdős #585, I wrote a formal statement with AI and [submitted it to the repository](https://github.com/google-deepmind/formal-conjectures/pull/6774). As of October 15, 2026, it has one approving review and is still open, with required review outstanding.

### 2. Decide what progress means

Once we had a way to check proofs, I needed a way to judge whether the results mattered. What would solving the problem look like? What would count as a useful partial result?

I created a scale, with solving the problem at one end and making no progress on the main question at the other (although every failed attempt is compost for the next endeavor!). I learned to be specific about what would not count. An early instruction to "prove something each round" produced easy special cases without moving the main question. I rewrote the goal to spell out the target, what would count as progress and what would not.

### 3. Build the harness

Then came the plumbing. I needed a way to connect the agents, their tools and the work they left behind. I worked with the agents to build what I call the math harness. It didn't exist in this form when I first attempted Erdős #585. I built it up over [many attempts](problems/585/findings/DECISIONS.md).

It brings together five things:

- **Tools:** scripts to run research sessions with deadlines, prepare literature searches, collect review results and rerun proof checks. The scripts save logs and results so I can see what actually happened.
- **Context management:** I give each agent a focused brief with the exact question, its assumptions, relevant sources and earlier failures. The agent needs enough context to work on its part of the problem and know how that connects to the larger question.
- **Memory management:** we save decisions, failed approaches, proof status and next steps outside the chat, with links back to the evidence. A new session can pick up from those records. I don't want each agent to spend its time rediscovering what the last one already tried.
- **Agent coordination:** I split work into research, proof writing, formalization and review. Reviewers start in fresh contexts and challenge the claims, check the assumptions and try to find counterexamples. Their job is to catch mistakes, and their agreement still isn't a proof.
- **Evaluation and stopping rules:** each attempt needs a target, evidence and a limit on how long to keep trying. I use the impact rubric to decide whether to continue, change direction or stop, and keep failed and unfinished attempts in the record.

Some steps are scripted; others still depend on me coordinating the agents. The records help me see where the process is working and where I need to step in.

### 4. Keep working on the big question

Now, with my math harness and impact rubric, I could go after partial results, check their claims and decide which direction deserved another attempt. The rubric helped me see when we were only improving a narrow case. I wanted a way to build from smaller useful results toward eventually solving these problems.

Here's a good example. I stopped an evolutionary search (a search that keeps the best attempts, tweaks them and tries again) after its control test timed out. In a separate comparison using the same compute budget, it also tied random search. Before scaling another search, I required a simple baseline to beat, an independent check of the results and a held-out test that hadn't been used to guide the search. The [decisions log](problems/585/findings/DECISIONS.md#attempt-2-october-1-to-4-scale) records that choice and how the process changed across the attempts.

In my own runs, I've now been able to leave agents working way longer without my intervention. I still step in to steer which questions matter and which directions are worth pursuing. My math harness has let me spend way less time on the administrative plumbing: reminding agents to save their work, check claims, stick to a budget, or return to the main question.

As we make more progress on Erdős's problems, I hope we can turn this math harness into a more general research harness, giving more people a way to contribute to scientific progress.

Enjoy.

## AI use

The formal statements, Lean proofs, written proofs, constructions and search programs in this
repository were produced with AI agents. The [problem pages](#collection) give their contribution and review details. I read the results, the checks and the claims they support.

I did not check the mathematics myself. I take full responsibility for any errors. No mathematician has reviewed the mathematics yet.

## Help needed

I am looking for help reviewing the manuscripts and written proofs linked from the [problem pages](#collection), particularly from mathematicians working in extremal graph theory. If you find an error, know of prior work or are willing to help, please open an issue. I'd love to get in contact with you.

## Collection

The collection starts with the completed case of #643, followed by partial results on the original questions and then separate theorem families. The counts below group headline results, not Lean helper declarations, proof modules or successive improvements of the same bound. They are not counts of new discoveries; the linked result pages give exact statements, attribution and additional supporting results.

| Problem | Manuscript | Contribution to the original question | Headline results, grouped | Verification |
|---|---|---|---|---|
| [643](problems/643/README.md) | [PDF](problems/643/manuscript/main.pdf) | **Settles the t = 3 asymptotic case.** Together with the attributed higher-uniformity preprint, completes the asymptotic question for every fixed t ≥ 3. | **1 main theorem + 2 consequence groups:** the sharp triple-system bound; its asymptotic consequence; exact extremal and forcing values at classical design orders. [Results and hypotheses](problems/643/RESULTS.md). | **Lean-verified:** the full triple-system theorem and both consequence groups, including the required design construction. The external higher-uniformity theorem is not Lean-verified here. |
| [583](problems/583/README.md) | [PDF](problems/583/manuscript.pdf) | **Partial result:** a universal saving in the leading coefficient for path partitions of connected finite simple graphs. Gallai's conjecture remains open. | **1 bound-improvement family:** the general and connected Eulerian partition bounds, with a formalization of the classical parity baseline. [Results and hypotheses](problems/583/RESULTS.md). | **Lean-verified:** both partition bounds and the supporting parity baseline, with original edges partitioned exactly. |
| [1017](problems/1017/README.md) | [PDF](problems/1017/manuscript/main.pdf) | **Partial results and a separate cost extremum:** finite bounds for fractional clique partitions and an integral lower construction. The original integral estimation problem remains open. | Density-dependent upper bounds; a prescribed-edge-count lower construction; an exact binomial-cost extremum; and an anchored-slope obstruction. [Results and hypotheses](problems/1017/RESULTS.md). | **Lean-verified:** five stated conclusions, with fractional, integral and binomial-cost scopes distinguished in the result index. |
| [60](problems/60/README.md) | [PDF](problems/60/manuscript/main.pdf) | **Partial result:** exact four-cycle counts and equality cases for specified orders and a restricted surplus range. The unrestricted problem remains open. | **2 theorem groups:** exact supersaturation with its lower bound and equality classification; first-excess structural control. The known extremal threshold is also formalized. [Results and hypotheses](problems/60/RESULTS.md). | **Lean-verified:** both theorem groups and the supporting extremal threshold, under their stated order and range hypotheses. |
| [642](problems/642/README.md) | [PDF](problems/642/manuscript/main.pdf) | **Partial result:** a cubic-logarithmic edge threshold forces a cycle with at least as many chords as vertices. The linear-threshold question remains open. A stronger announced result limits the prior-work comparison; no current-best or priority claim is made. | **1 main bound development:** the cubic-logarithmic theorem, three earlier whole-graph bounds and six supporting statements. [Results and hypotheses](problems/642/RESULTS.md). | **Lean-verified:** the stated whole-graph bounds and six supporting statements, under their recorded hypotheses. Successive bounds are not separate solutions. |
| [585](problems/585/README.md) | [PDF](problems/585/manuscript/main.pdf) | **Separate theorem families and finite cases.** These do not improve the original problem's known asymptotic bounds. | **2 regular-subgraph theorem families:** sufficient conditions and avoiding constructions. Additional exact small values, lower witnesses and finite computations are listed separately. [Results and hypotheses](problems/585/RESULTS.md). | **Lean-verified:** the stated regular-subgraph bounds, avoiding constructions and registered finite results. Computational upper exclusions and written candidates have separate evidence labels. |
| [85](problems/85/README.md) | [PDF](problems/85/manuscript/main.pdf) | **Separate theorem:** projective-incidence repair. The original eventual-monotonicity question remains open. | **1 main theorem + 2 formal corollaries:** coupled point–hyperplane repair, its dichotomy and its no-field-embedding bound. [Results and hypotheses](problems/85/RESULTS.md). | **Lean-verified:** the full repair theorem and both formal corollaries, under the explicit frame-survival/error hypothesis. |

Lean verification checks the stated mathematics; it does not establish novelty or human review. The classical constructions and external results retain their attribution. No human mathematical review is claimed. Apart from the stated #643 asymptotic conclusion, the packages do not settle their original Erdős problems.

## Documentation

| Guide | What it covers |
|---|---|
| [Verification](docs/verification.md) | What each kind of evidence establishes and how to reproduce the checks. |
| [AI methods](docs/ai-methods.md) | How AI agents contribute and how their work is reviewed. |
| [Contributing](CONTRIBUTING.md) | Corrections, mathematical review and references to prior work. |
| [Repository layout](docs/migration.md) | Where files live and how historical paths map to the collection. |
| [Adding a problem](docs/adding-a-problem.md) | Required files, statement details and verification records. |

## License and citation

Apache-2.0 is the collection default, with explicit package exceptions and third-party notices retained. The combined #643 design proof package is GPLv3; individual Apache-origin source notices remain intact. See [LICENSE](LICENSE), [NOTICE](NOTICE) and the [collection citation](CITATION.cff). Cite a particular result using its problem’s own citation and declaration or source file.
