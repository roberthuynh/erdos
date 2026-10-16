import Openmath.Erdos643.AllStarDeletion
import Openmath.Erdos643.ProjectionBridge

namespace Erdos643.FinalBound
open Finset HypergraphBasics Projection TriangleCleanup K5Cleaning
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable local instance (G : SimpleGraph V) : Fintype G.edgeSet := Fintype.ofFinite _

lemma edge_pair_card {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    e.toFinset.card = 2 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp he
    simp [Sym2.toFinset_mk_eq, G.ne_of_adj hxy]

lemma xcharge_eq {H : TripleSystem V} (hu : Uniform H) :
    AllStarDeletion.XChargePairs (projected H) = ProjectionBridge.XCharges (projected H) := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨e,he,rfl⟩ := mem_image.mp hS
    have hc := edge_pair_card he
    obtain ⟨x,y,hxy,heq⟩ := card_eq_two.mp hc
    have hm : {x,y} ∈ AllStarDeletion.XChargePairs (projected H) := by
      rw [← heq]; exact mem_image.mpr ⟨e,he,rfl⟩
    have ha := AllStarDeletion.mem_XChargePairs.mp hm
    apply mem_filter.mpr
    exact ⟨mem_powersetCard.mpr ⟨subset_univ _,hc⟩,x,y,heq,ha⟩
  · intro hS
    obtain ⟨_,x,y,he,ha⟩ := mem_filter.mp hS
    rw [he]
    exact AllStarDeletion.mem_XChargePairs.mpr ha

lemma ycharge_eq {H : TripleSystem V} (hu : Uniform H) :
    AllStarDeletion.YChargePairs (projected H) = ProjectionBridge.YCharges (projected H) := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨e,he,rfl⟩ := mem_image.mp hS
    have hc := edge_pair_card he
    obtain ⟨x,y,hxy,heq⟩ := card_eq_two.mp hc
    have hm : {x,y} ∈ AllStarDeletion.YChargePairs (projected H) := by
      rw [← heq]; exact mem_image.mpr ⟨e,he,rfl⟩
    have ha := AllStarDeletion.mem_YChargePairs.mp hm
    apply mem_filter.mpr
    exact ⟨mem_powersetCard.mpr ⟨subset_univ _,hc⟩,x,y,heq,ha⟩
  · intro hS
    obtain ⟨_,x,y,he,ha⟩ := mem_filter.mp hS
    rw [he]
    exact AllStarDeletion.mem_YChargePairs.mpr ha

/-- Complete actual all-star inequality, using the proved owner deletion and
original B/D pair identities. No deletion-cost hypothesis is assumed. -/
theorem allstar_pair_bound {H : TripleSystem V} (hu : Uniform H) (hs : AllStars H) :
    3 * H.card ≤ (Fintype.card V).choose 2 + (Bpairs H).card + (Dpairs H).card := by
  classical
  have hv : AllStarDeletion.Valid (projected H) := by
    intro z hz
    exact (projected_pair hu hz).1
  have hx : AllStarDeletion.XStars (projected H) := by
    intro x y hxy hne
    exact ProjectionBridge.projected_x_stars hu hs hxy
  have ht : AllStarDeletion.Transport (projected H) := by
    intro u v huv hne
    exact ProjectionBridge.projected_y_transport hu hs huv
  obtain ⟨R,hR,hcost,hunique⟩ := AllStarDeletion.allStar_deletion (projected H) hv hx ht
  rw [xcharge_eq hu,ycharge_eq hu,ProjectionBridge.xcharges_eq_Bpairs hu,
    ProjectionBridge.ycharges_eq_Dpairs hu] at hcost
  let U := projected H \ R
  have hmap : Set.MapsTo (Prod.snd : V × Finset V → Finset V)
      (↑U : Set (V × Finset V)) (↑((univ : Finset V).powersetCard 2) : Set (Finset V)) := by
    intro z hz
    exact mem_powersetCard.mpr ⟨subset_univ _,(projected_pair hu (sdiff_subset hz)).1⟩
  have hinj : Set.InjOn (Prod.snd : V × Finset V → Finset V) (↑U : Set (V × Finset V)) := by
    intro p hp q hq hpq
    have hf : p.1 = q.1 := hunique p.1 q.1 p.2 hp (by simpa only [hpq,Prod.eta] using (show q ∈ projected H \ R from hq))
    exact Prod.ext hf hpq
  have hsmall : U.card ≤ (Fintype.card V).choose 2 := by
    simpa using card_le_card_of_injOn (Prod.snd : V × Finset V → Finset V) hmap hinj
  have hc := card_sdiff_add_card_eq_card hR
  have hp := projected_card hu
  change U.card + R.card = (projected H).card at hc
  omega

lemma literal_mono {H G : TripleSystem V} (hGH : G ⊆ H) (ha : LiteralAvoids H) :
    LiteralAvoids G := by
  intro A hA B hB C hC D hD hAB hCD he
  exact ha A (hGH hA) B (hGH hB) C (hGH hC) D (hGH hD) hAB hCD he

/-- Every finite simple3graph avoiding exactly four distinct actual triples
with both pairs disjoint and equal six-vertex union satisfies the4/3 bound. -/
theorem three_card_le_four_choose (H : TripleSystem V) (hu : Uniform H)
    (hno : ¬ Forbidden H) :
    3 * H.card ≤ 4 * (Fintype.card V).choose 2 := by
  classical
  have ha : LiteralAvoids H := (literalAvoids_iff_not_forbidden hu).mpr hno
  obtain ⟨R,hR,hK,hbudget⟩ := pv2009_lemma11 H hu ha
  let G := H \ R
  have huG : Uniform G := fun E hE => hu E (sdiff_subset hE)
  have haG : LiteralAvoids G := literal_mono sdiff_subset ha
  obtain ⟨Z,hZ,hzc,hs⟩ := triangle_cleanup huG haG hK
  let J := G \ Z
  have huJ : Uniform J := fun E hE => huG E (sdiff_subset hE)
  have hstar := allstar_pair_bound huJ hs
  have hbmono := card_le_card (Bpairs_mono (show J ⊆ G from sdiff_subset))
  have hdmono := card_le_card (Dpairs_mono (show J ⊆ G from sdiff_subset))
  have hdb := card_le_card (Dpairs_subset_Bpairs G)
  have hcH : G.card + R.card = H.card := card_sdiff_add_card_eq_card hR
  have hcG : J.card + Z.card = G.card := card_sdiff_add_card_eq_card hZ
  change (Bpairs G).card + R.card ≤ (Fintype.card V).choose 2 at hbudget
  nlinarith

/-- Integer/floor form of the actual original-pattern upper bound. -/
theorem card_le_floor_four_thirds (H : TripleSystem V) (hu : Uniform H)
    (hno : ¬ Forbidden H) :
    H.card ≤ (4 * (Fintype.card V).choose 2) / 3 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
  simpa only [Nat.mul_comm] using three_card_le_four_choose H hu hno

end Erdos643.FinalBound
