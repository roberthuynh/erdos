import Openmath.Proofs.PaperSupport.QB6FinalAssemblyPrep
import Openmath.Proofs.PaperSupport.QB6C02MinFive

/-! Unconditional QB6. The original minimum-five producer is a closed proved
term; the conditional adapter's last producer premise is discharged here.
The public endpoint uses only the original finite graph hypotheses. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Erdos585.QB6Unconditional
universe u

theorem minfive_literal : QB6FinalAssemblyPrep.LiteralMinFiveC02Repair.{u} :=
  QB6C02MinFive.minfive_repair

theorem c02_repair : QB6Assembly.C02Repair.{u} :=
  QB6FinalAssemblyPrep.c02_repair_from_minfive minfive_literal

open scoped Classical in
/-- Every original finite bipartite cap-six host at e >= 3n - 6 contains a
nonempty four-regular subgraph. No physical producer is a premise. -/
theorem qb6 {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hbip : G.IsBipartite) (hdeg : G.maxDegree ≤ 6) (hn : 4 ≤ Fintype.card V)
    (he : 3 * Fintype.card V ≤ G.edgeSet.ncard + 6) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4 :=
  QB6FinalAssemblyPrep.qb6_graph_from_minfive minfive_literal G hbip hdeg hn he

#print axioms minfive_literal
#print axioms c02_repair
#print axioms qb6
end Erdos585.QB6Unconditional
