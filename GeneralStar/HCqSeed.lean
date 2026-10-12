import GeneralStar.UniformSeed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

theorem hcq_order (q : ℕ) : (hcqSeed q).order=2*q+7 := by
  change Fintype.card (L17HCq.SeedVertex q)=2*q+7
  simp [L17HCq.SeedVertex,L17HCq.SeedLeft,L17HCq.SeedRight,Fintype.card_sum];omega

theorem hcq_slots (q : ℕ) (hq : 5 ≤ q) :
    (q-1)^2 ≤ ∑ v ∈ (hcqSeed q).B,(2*(q-1)-(hcqSeed q).graph.degree v) := by
  let D := hcqSeed q
  have hg := L17HCq.hcq_seed_good q hq
  have hc : D.B.card=q+4 := by
    change (L17HCq.hcqSeedB q).card=q+4
    simp [L17HCq.hcqSeedB,card_image_of_injective _ Sum.inr_injective,
      L17HCq.SeedRight,Fintype.card_sum]
  have hcapacity : (∑ v ∈ D.B,(2*(q-1)-D.graph.degree v))+D.graph.edgeFinset.card=
      2*(q-1)*(q+4) := by
    calc
      _ = (∑ v ∈ D.B,(2*(q-1)-D.graph.degree v))+∑ v ∈ D.B,D.graph.degree v := by
        have he : (∑ v ∈ D.B,D.graph.degree v)=D.graph.edgeFinset.card :=
          SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hg.bipartite
        rw [he]
      _ = ∑ _v ∈ D.B,2*(q-1) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro v _
        exact Nat.sub_add_cancel (hg.degree_bounds v).2
      _ = _ := by simp [hc,mul_comm]
  have he := L17HCq.hcq_seed_edge_count q hq
  change D.graph.edgeFinset.card+5=q*q+7*q at he
  have hr : q-1+1=q := by omega
  nlinarith

theorem hcq_seedHyp (q : ℕ) (hq : 5 ≤ q) : SeedHyp q (hcqSeed q) := by
  have h := L17HCq.hcq_seed_good q hq
  exact ⟨h.disjoint,h.cover,h.bipartite,h.degree_bounds,h.no_regular,hcq_slots q hq⟩

theorem hcq_deficit (q : ℕ) (hq : 5 ≤ q) :
    (q-1)*(hcqSeed q).order-(hcqSeed q).graph.edgeFinset.card=(q-1)^2-3 := by
  rw [hcq_order]
  have he := L17HCq.hcq_seed_edge_count q hq
  have hr : q-1+1=q := by omega
  have hs : 3 ≤ (q-1)^2 := by nlinarith
  have hsub : (q-1)^2-3+3=(q-1)^2 := by omega
  have hadd : (hcqSeed q).graph.edgeFinset.card+((q-1)^2-3)=(q-1)*(2*q+7) := by
    change (L17HCq.hcqSeedGraph q).edgeFinset.card+((q-1)^2-3)=(q-1)*(2*q+7)
    nlinarith
  omega

end Erdos585.GeneralStar
