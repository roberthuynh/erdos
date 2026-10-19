# Combined design proof package notices

The combined design proof program is prepared under GNU GPL version 3, whose
complete text is in COPYING. Original Apache-2.0 source files retain their
existing copyright/license notices; LICENSE.upstream remains unchanged.

Some finite difference-matrix witness tables in this design proof package
are derived from SageMath. The retained Sage source revision is
`adff41bc98ebbe47fc5c4dc7d794bfc1957d6365`. The original library terms permit
GPL version 2 or, at the recipient's option, a later version. This package elects
GPL version 3 for the derived witness modules and combined proof program.
The exact retained Sage copyright/license statement is in
licenses/Sage-COPYING.txt. The original sources are distributed without warranty;
the full applicable terms are retained in those license files.

Source: SageMath `src/sage/combinat/designs/database.py` at that revision,
SHA-256 `55a30e8aebba5b1d34f8e6469dad746a42757b1c2c549715a04b00069be423a9`.
The table origins are:

- `DM_21_6_1`, lines 3272–3305, credits Handbook of Combinatorial Designs,
  III.3.50, and supplies a finite seed array and cyclic development.
- `DM_60_6_1`, lines 3974–4023, credits R. Julian R. Abel, Existence of Five
  MOLS of Orders 18 and 60, Journal of Combinatorial Designs,
  DOI 10.1002/jcd.21384, and supplies an array over Z₂×Z₃₀ and its development.

The Lean adaptation, prepared on 20 October 2026, replaces execution of the Sage implementation with explicit
finite witness data and mathematical pair-coverage proofs. Modified Lean
representations and exact original-to-export hashes are inventoried in
design-source-provenance.json. Direct derived-table modules are
Openmath/Erdos643Design/TD21.lean and TD60.lean; TD84.lean and
TDCompositeSeeds.lean build on those derived tables. All combined-source module
boundaries are recorded by the complete source manifests and target import graph.

Upstream dependency licenses remain applicable; pinned revisions are listed
in lake-manifest.json. Cited research articles are not redistributed with the
source code. Individual Apache-origin source files retain their original
copyright and license notices.
