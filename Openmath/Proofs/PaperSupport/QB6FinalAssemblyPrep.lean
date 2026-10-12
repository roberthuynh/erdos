import Openmath.Proofs.PaperSupport.QB6Assembly
import Openmath.Proofs.PaperSupport.QB6C3S
import Openmath.Proofs.PaperSupport.QB6E6Result
import Openmath.Proofs.PaperSupport.QB6C02One4

/-! Conditional universal QB6 adapter. Exactly the literal minimum-five C02
producer remains an input. C3S/E6 and the original-degree-four C02 case are
closed actual graph producers. A clean conditional check does not remove
this last premise or claim unconditional QB6. -/
open Finset
open Erdos585.QB4 Erdos585.QB5 Erdos585.QB6Assembly
open Erdos585.QB6C02Five4 Erdos585.QB6C02One4
namespace Erdos585.QB6FinalAssemblyPrep
universe u
set_option maxHeartbeats 1000000

def LiteralMinFiveC02Repair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → (∀ a ∈ A, 5 ≤ dg G C a) → Quartic G A C

open scoped Classical in
def UniversalQB6 : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), G.IsBipartite → G.maxDegree ≤ 6 →
    4 ≤ Fintype.card V → 3 * Fintype.card V ≤ G.edgeSet.ncard + 6 →
      ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4

/-- Both C02 sides use the original graph and the original C degrees. -/
theorem c02_repair_from_minfive (repairMin5 : LiteralMinFiveC02Repair.{u}) :
    C02Repair.{u} := by
  intro V _ G _ A C h
  classical
  by_cases hfour : 1 ≤ #(degreeFourRows G A C)
  · exact one4_repair G A C h hfour
  · have hfive : ∀ a ∈ A, 5 ≤ dg G C a := by
      intro a ha
      have hlo := h.minA a ha
      by_contra hn
      have he : dg G C a = 4 := by omega
      have hD : a ∈ degreeFourRows G A C := mem_degreeFourRows.mpr ⟨ha, he⟩
      have hc := card_pos.mpr ⟨a, hD⟩
      omega
    exact repairMin5 G A C h hfive

/-- Actual arbitrary finite support version, with only the minimum-five producer unpaid. -/
theorem quartic_from_minfive (repairMin5 : LiteralMinFiveC02Repair.{u})
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {X Y : Finset V} (hd : Disjoint X Y)
    (hcapX : ∀ x ∈ X, dg G Y x ≤ 6) (hcapY : ∀ y ∈ Y, dg G X y ≤ 6)
    (hn : 4 ≤ #X + #Y) (hg : gv G X Y ≤ 12) : Quartic G X Y :=
  quartic_of_gv_le_twelve (c02_repair_from_minfive repairMin5)
    Erdos585.QB6C3S.c3s_repair Erdos585.QB6E6Result.e6_repair hd hcapX hcapY hn hg

/-- Exactly one literal original graph producer is still a premise. -/
theorem qb6_conditional_minfive (repairMin5 : LiteralMinFiveC02Repair.{u}) :
    UniversalQB6.{u} := by
  intro V _ G hbip hdeg hn he
  exact qb6_conditional_direct (c02_repair_from_minfive repairMin5)
    Erdos585.QB6C3S.c3s_repair Erdos585.QB6E6Result.e6_repair G hbip hdeg hn he

open scoped Classical in
/-- Expanded original host endpoint, with no shore or extraction suppliers. -/
theorem qb6_graph_from_minfive (repairMin5 : LiteralMinFiveC02Repair.{u})
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hdeg : G.maxDegree ≤ 6) (hn : 4 ≤ Fintype.card V)
    (he : 3 * Fintype.card V ≤ G.edgeSet.ncard + 6) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4 :=
  qb6_conditional_minfive repairMin5 G hbip hdeg hn he

#print axioms c02_repair_from_minfive
#print axioms quartic_from_minfive
#print axioms qb6_conditional_minfive
#print axioms qb6_graph_from_minfive
end Erdos585.QB6FinalAssemblyPrep
