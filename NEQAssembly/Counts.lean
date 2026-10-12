import NEQAssembly.Transport

/-! Original edge-count preservation and thinning.
Every image uses an actual graph embedding; thinning chooses original edges. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.NEQAssembly
open QB4 B5 NEQ
universe u v

lemma dg_embedding_image {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (K : SimpleGraph A) (G : SimpleGraph B)
    (f : K ↪g G) (X : Finset A) (a : A) :
    dg G (X.image f) (f a) = dg K X a := by
  unfold dg
  symm
  apply card_bij (fun (b : A) _ => f b)
  · intro b hb
    obtain ⟨hbX, hab⟩ := mem_filter.mp hb
    exact mem_filter.mpr ⟨mem_image_of_mem f hbX, f.map_adj_iff.mpr hab⟩
  · intro b _ c _ hbc
    exact f.injective hbc
  · intro b hb
    obtain ⟨hbX, hab⟩ := mem_filter.mp hb
    obtain ⟨c, hcX, rfl⟩ := mem_image.mp hbX
    exact ⟨c, mem_filter.mpr ⟨hcX, f.map_adj_iff.mp hab⟩, rfl⟩

lemma ec_embedding_image {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (K : SimpleGraph A) (G : SimpleGraph B)
    (f : K ↪g G) (X Y : Finset A) :
    ec G (X.image f) (Y.image f) = ec K X Y := by
  unfold ec
  rw [sum_image (fun a _ b _ hab => f.injective hab)]
  exact sum_congr rfl (fun a _ => dg_embedding_image K G f Y a)

lemma dg_mono_original {V : Type u} [Fintype V] [DecidableEq V]
    (K G : SimpleGraph V) (hsub : K ≤ G) (X : Finset V) (v : V) :
    dg K X v ≤ dg G X v := by
  unfold dg
  apply card_le_card
  intro w hw
  obtain ⟨hwX, hkw⟩ := mem_filter.mp hw
  exact mem_filter.mpr ⟨hwX, hsub hkw⟩

lemma ec_mono_original {V : Type u} [Fintype V] [DecidableEq V]
    (K G : SimpleGraph V) (hsub : K ≤ G) (X Y : Finset V) :
    ec K X Y ≤ ec G X Y := by
  exact sum_le_sum (fun v _ => dg_mono_original K G hsub Y v)

lemma induced_cap {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (D : ℕ) (hcap : G.maxDegree ≤ D) :
    (G.induce (U : Set V)).maxDegree ≤ D := by
  apply maxDegree_le_of_forall_degree_le
  intro v
  rw [induced_degree_eq_dg]
  exact (dg_le_maxDegree U v).trans hcap

lemma thinned_cap {V : Type u} [Fintype V] [DecidableEq V]
    (K G : SimpleGraph V) (D : ℕ) (hsub : K ≤ G) (hcap : G.maxDegree ≤ D) :
    K.maxDegree ≤ D := by
  apply maxDegree_le_of_forall_degree_le
  intro v
  exact (degree_le_of_le hsub).trans ((G.degree_le_maxDegree v).trans hcap)

lemma edgeFinset_ncard {V : Type u} [Fintype V] (G : SimpleGraph V) :
    #G.edgeFinset = G.edgeSet.ncard := by
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

theorem original_edge_thinning {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m : ℕ) (hm : m ≤ G.edgeSet.ncard) :
    ∃ K : SimpleGraph V, K ≤ G ∧ K.edgeSet.ncard = m := by
  have hm' : m ≤ #G.edgeFinset := by rw [edgeFinset_ncard]; exact hm
  obtain ⟨E, hE, hcard⟩ := exists_subset_card_eq hm'
  have hsub : (E : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    exact (G.mem_edgeFinset).mp (hE he)
  have hdis : Disjoint (E : Set (Sym2 V)) Sym2.diagSet :=
    Set.disjoint_left.mpr (fun e he hd => G.edgeSet_subset_compl_diagSet (hsub he) hd)
  let K : SimpleGraph V := fromEdgeSet (E : Set (Sym2 V))
  have hedge : K.edgeSet = (E : Set (Sym2 V)) :=
    (edgeSet_eq_iff K (E : Set (Sym2 V))).mpr ⟨rfl, hdis⟩
  refine ⟨K, ?_, ?_⟩
  · exact (edgeSet_subset_edgeSet).mp (by rw [hedge]; exact hsub)
  · rw [hedge]
    simpa using hcard

#print axioms dg_embedding_image
#print axioms ec_embedding_image
#print axioms dg_mono_original
#print axioms ec_mono_original
#print axioms induced_cap
#print axioms thinned_cap
#print axioms edgeFinset_ncard
#print axioms original_edge_thinning
end Erdos585.NEQAssembly
