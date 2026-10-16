import R856.Main
import R838.Main
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R866
open QB4 B5 R837 NEQAssembly
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) (S : Support V)

abbrev Carrier := ((S.1 ∪ S.2 : Finset V) : Set V)
def sideA : Finset (Carrier S) := univ.filter fun x => x.val ∈ S.1
def sideB : Finset (Carrier S) := univ.filter fun x => x.val ∈ S.2

lemma image_sideA : (sideA S).image Subtype.val = S.1 := by
  ext v
  simp only [sideA,mem_image,mem_filter,mem_univ,true_and,Subtype.exists]
  constructor
  · rintro ⟨a,ha,hA,rfl⟩; exact hA
  · intro hv
    exact ⟨v,mem_union_left _ hv,hv,rfl⟩
lemma image_sideB : (sideB S).image Subtype.val = S.2 := by
  ext v
  simp only [sideB,mem_image,mem_filter,mem_univ,true_and,Subtype.exists]
  constructor
  · rintro ⟨a,ha,hB,rfl⟩; exact hB
  · intro hv
    exact ⟨v,mem_union_right _ hv,hv,rfl⟩
lemma sides_cover : sideA S ∪ sideB S = univ := by
  ext v
  simpa [sideA,sideB] using v.property
lemma sides_disjoint (hd : Disjoint S.1 S.2) : Disjoint (sideA S) (sideB S) := by
  apply Finset.disjoint_left.mpr
  intro v ha hb
  exact disjoint_left.mp hd (mem_filter.mp ha).2 (mem_filter.mp hb).2
lemma card_sideA : #(sideA S) = #S.1 := by
  rw [← image_sideA S,card_image_of_injective _ Subtype.val_injective]
lemma card_sideB : #(sideB S) = #S.2 := by
  rw [← image_sideB S,card_image_of_injective _ Subtype.val_injective]
lemma carrier_order (hd : Disjoint S.1 S.2) : Fintype.card (Carrier S)=order S := by
  change Fintype.card ↥(S.1 ∪ S.2) = order S
  rw [Fintype.card_coe,card_union_of_disjoint hd]
  rfl

lemma carrier_bipartite (hb : InducedBipartite G S) :
    (G.induce (Carrier S)).IsBipartiteWith (sideA S : Set (Carrier S)) (sideB S) := by
  refine ⟨by simpa only [Finset.disjoint_coe] using sides_disjoint S hb.1,?_⟩
  intro v w he
  have hv := v.property
  have hw := w.property
  rcases mem_union.mp hv with va | vb <;> rcases mem_union.mp hw with wa | wb
  · exact False.elim (hb.2.1 v.val va w.val wa he)
  · exact Or.inl ⟨by simpa [sideA] using va,by simpa [sideB] using wb⟩
  · exact Or.inr ⟨by simpa [sideB] using vb,by simpa [sideA] using wa⟩
  · exact False.elim (hb.2.2 v.val vb w.val wb he)

lemma carrier_degree_left (hb : InducedBipartite G S) (v : Carrier S)
    (hv : v ∈ sideA S) : (G.induce (Carrier S)).degree v = dg G S.2 v := by
  rw [← dg_eq_degree (carrier_bipartite G S hb) hv]
  have he := dg_embedding_image (G.induce (Carrier S)) G
    (Embedding.induce (G := G) (Carrier S)) (sideB S) v
  change dg G ((sideB S).image Subtype.val) v.val = _ at he
  rw [image_sideB] at he
  exact he.symm
lemma carrier_degree_right (hb : InducedBipartite G S) (v : Carrier S)
    (hv : v ∈ sideB S) : (G.induce (Carrier S)).degree v = dg G S.1 v := by
  rw [← dg_eq_degree (carrier_bipartite G S hb).symm hv]
  have he := dg_embedding_image (G.induce (Carrier S)) G
    (Embedding.induce (G := G) (Carrier S)) (sideA S) v
  change dg G ((sideA S).image Subtype.val) v.val = _ at he
  rw [image_sideA] at he
  exact he.symm

lemma carrier_deficit (hb : InducedBipartite G S) {q : ℕ} (hq : 1 ≤ q) :
    ((q:ℤ)-1)*Fintype.card (Carrier S)-
      ((G.induce (Carrier S)).edgeSet.ncard:ℤ) = deficit G (q-1) S := by
  have he := ec_embedding_image (G.induce (Carrier S)) G
    (Embedding.induce (G := G) (Carrier S)) (sideA S) (sideB S)
  change ec G ((sideA S).image Subtype.val) ((sideB S).image Subtype.val) = _ at he
  rw [image_sideA,image_sideB] at he
  have hc : (G.induce (Carrier S)).edgeSet.ncard = ec G S.1 S.2 :=
    (ec_eq_ncard (carrier_bipartite G S hb)).symm.trans he.symm
  rw [hc,carrier_order S hb.1]
  unfold deficit
  have hpred : ((q-1:ℕ):ℤ)=(q:ℤ)-1 := by omega
  rw [hpred]

lemma carrier_subset_floor (hb : InducedBipartite G S) {h q : ℕ} {F : ℤ}
    (hq : 1 ≤ q)
    (hf : ∀ T, Included T S → h ≤ order T → order T < order S →
      F ≤ deficit G (q-1) T) :
    ∀ D : Finset (Carrier S), h ≤ #D → #D < Fintype.card (Carrier S) →
      F ≤ ((q:ℤ)-1)*#D-((G.induce (Carrier S)).induce (D : Set (Carrier S))).edgeSet.ncard := by
  intro D hd hp
  let X := sideA S ∩ D
  let Y := sideB S ∩ D
  let T : Support V := (X.image Subtype.val,Y.image Subtype.val)
  have hx : X ⊆ sideA S := inter_subset_left
  have hy : Y ⊆ sideB S := inter_subset_left
  have hinc : Included T S := by
    constructor
    · exact (Finset.image_mono _ hx).trans (by rw [image_sideA])
    · exact (Finset.image_mono _ hy).trans (by rw [image_sideB])
  have hdis := (sides_disjoint S hb.1).mono hx hy
  have hxy : X ∪ Y = D := by
    dsimp [X,Y]
    rw [← union_inter_distrib_right,sides_cover,univ_inter]
  have hc : order T = #D := by
    dsimp [T,order]
    rw [card_image_of_injective _ Subtype.val_injective,
      card_image_of_injective _ Subtype.val_injective,← card_union_of_disjoint hdis,hxy]
  have fl := hf T hinc (by omega) (by rw [← carrier_order S hb.1];omega)
  have he := ec_embedding_image (G.induce (Carrier S)) G
    (Embedding.induce (G := G) (Carrier S)) X Y
  change ec G (X.image Subtype.val) (Y.image Subtype.val) = _ at he
  have hed : ((G.induce (Carrier S)).induce (D : Set (Carrier S))).edgeSet.ncard =
      ec G T.1 T.2 := by
    rw [← hxy,H3Unequal.induced_edges_eq_ec (sides_disjoint S hb.1)
      (carrier_bipartite G S hb) hx hy]
    exact he.symm
  rw [hed]
  have hpred : ((q-1:ℕ):ℤ)=(q:ℤ)-1 := by omega
  simpa only [deficit,hpred,hc] using fl

end Erdos585.R866
