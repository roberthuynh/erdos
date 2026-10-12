import GeneralStar.Shores

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

theorem seed_edge_bound (q : ℕ) (D : GraphData) (hs : SeedHyp q D) :
    D.graph.edgeFinset.card ≤ (q-1)*D.order := by
  have hsum : (∑ v : D.Carrier, D.graph.degree v) ≤
      (∑ _v : D.Carrier, 2*(q-1)) := sum_le_sum (fun v _ => (hs.2.2.2.1 v).2)
  rw [D.graph.sum_degrees_eq_twice_card_edges] at hsum
  simp only [sum_const,card_univ,nsmul_eq_mul] at hsum
  change 2*D.graph.edgeFinset.card ≤ D.order*(2*(q-1)) at hsum
  nlinarith

/-- T24: the faithful actual graph transfer, including every partial newborn block.
The only seed hypotheses here are the explicitly allowed generic T24 contract. -/
theorem T24 (q : ℕ) (D : GraphData) (hq : 5 ≤ q) (hs : SeedHyp q D) (t : ℕ) :
    FamilyConclusion q (D.order+t) ((q-1)*D.order-D.graph.edgeFinset.card)
      (transferState q D t) := by
  refine ⟨transfer_order q D t,?_,transfer_min q D hq hs t,?_,?_,transfer_noRegular q D hq hs t⟩
  · exact (transfer_bipartiteWith q D hq hs t).isBipartite
  · have hm := (transferState q D t).graph.maxDegree_le_of_forall_degree_le
      (2*(q-1)) (transfer_max q D hq hs t)
    have he : 2*(q-1)=2*q-2 := by omega
    simpa only [he] using hm
  · rw [transfer_edges q D hq hs t]
    have hb := seed_edge_bound q D hs
    have he : (q-1)*(D.order+t)=(q-1)*D.order+(q-1)*t := by ring
    rw [he]
    omega

theorem T24_order (q : ℕ) (D : GraphData) (hq : 5 ≤ q) (hs : SeedHyp q D)
    (n : ℕ) (hn : D.order ≤ n) :
    FamilyConclusion q n ((q-1)*D.order-D.graph.edgeFinset.card)
      (transferState q D (n-D.order)) := by
  have h := T24 q D hq hs (n-D.order)
  have he : D.order+(n-D.order)=n := by omega
  simpa only [he] using h

end Erdos585.GeneralStar
