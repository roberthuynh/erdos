import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.LocalCodegreeIncidence
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CodegreeLayerCake
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.AvoidanceHeredity
import Openmath.Erdos642.Proofs.CampaignFe72210b.BipartiteSigns

/-! Actual embedded threshold incidence graphs and avoidance-derived P8 density. -/
namespace Erdos642.CampaignFe72210bContinuation3.LocalCodegreeSubgraph
open Erdos642.CampaignFe72210b
open FourthReturnExpansion LocalCodegreeIncidence
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def codegree (v w : V) : ℕ := Fintype.card (G.commonNeighbors v w)
noncomputable def layer (v : V) (j : ℕ) : Finset V :=
  CodegreeLayerCake.threshold (Finset.univ.erase v) (codegree G v) j
abbrev LocalVertex (v : V) (j : ℕ) := (G.neighborFinset v) ⊕ (layer G v j)

noncomputable def incidenceGraph (v : V) (j : ℕ) : SimpleGraph (LocalVertex G v j) where
  Adj a b := match a,b with
    | Sum.inl x, Sum.inr w => G.Adj x.val w.val
    | Sum.inr w, Sum.inl x => G.Adj x.val w.val
    | _,_ => False
  symm := ⟨by intro a b hab; cases a <;> cases b <;> exact hab⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

noncomputable instance incidenceGraph_decidableAdj (v : V) (j : ℕ) :
    DecidableRel (incidenceGraph G v j).Adj := Classical.decRel _

noncomputable def vertexMap (v : V) (j : ℕ) : LocalVertex G v j → V
  | Sum.inl x => x.val
  | Sum.inr w => w.val

noncomputable def incidenceHom (v : V) (j : ℕ) : incidenceGraph G v j →g G where
  toFun := vertexMap G v j
  map_rel' := by
    intro a b hab
    cases a <;> cases b
    all_goals change _ at hab
    · exact False.elim hab
    · exact hab
    · exact (show G.Adj _ _ from hab).symm
    · exact False.elim hab

theorem neighbor_layer_disjoint (hbip : G.IsBipartite) (v : V) (j : ℕ) (hj : 1 ≤ j) :
    Disjoint (G.neighborFinset v) (layer G v j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hw hW
  have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  have hcw : 1 ≤ codegree G v w := hj.trans (Finset.mem_filter.mp hW).2
  have hne : (G.commonNeighbors v w).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    have hz : codegree G v w = 0 := by simp [codegree, he]
    omega
  obtain ⟨x,hx⟩ := hne
  have hvx : G.Adj v x := hx.1
  have hwx : G.Adj w x := hx.2
  obtain ⟨σ,hσ,hflip⟩ := exists_bipartite_sign G hbip
  have h1 := hflip v w hvw
  have h2 := hflip v x hvx
  have h3 := hflip w x hwx
  nlinarith [hσ v]

theorem incidenceHom_injective (hbip : G.IsBipartite) (v : V) (j : ℕ) (hj : 1 ≤ j) :
    Function.Injective (incidenceHom G v j) := by
  intro a b hab
  have hd := neighbor_layer_disjoint G hbip v j hj
  cases a with
  | inl x =>
    cases b with
    | inl y => exact congrArg Sum.inl (Subtype.ext hab)
    | inr w =>
      change x.val = w.val at hab
      have hx : x.val ∈ layer G v j := hab.symm ▸ w.property
      exact False.elim (Finset.disjoint_left.mp hd x.property hx)
  | inr w =>
    cases b with
    | inl x =>
      change w.val = x.val at hab
      have hw : w.val ∈ G.neighborFinset v := hab.symm ▸ x.property
      exact False.elim (Finset.disjoint_left.mp hd hw w.property)
    | inr z => exact congrArg Sum.inr (Subtype.ext hab)

noncomputable def rightNeighborEquiv (v : V) (j : ℕ) (w : layer G v j) :
    (incidenceGraph G v j).neighborSet (Sum.inr w) ≃ G.commonNeighbors v w.val where
  toFun z := by
    rcases z with ⟨a,ha⟩
    cases a with
    | inl x => exact ⟨x.val, (G.mem_neighborFinset v x.val).mp x.property, ha.symm⟩
    | inr q => exact False.elim ha
  invFun x := ⟨Sum.inl ⟨x.val,(G.mem_neighborFinset v x.val).mpr x.property.1⟩,
    x.property.2.symm⟩
  left_inv := by
    intro z
    rcases z with ⟨a,ha⟩
    cases a with
    | inl x => rfl
    | inr q => exact False.elim ha
  right_inv := by intro x; rfl

theorem right_degree (v : V) (j : ℕ) (w : layer G v j) :
    (incidenceGraph G v j).degree (Sum.inr w) = codegree G v w.val := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (rightNeighborEquiv G v j w)

noncomputable def leftPart (v : V) (j : ℕ) : Finset (LocalVertex G v j) := Finset.univ.image Sum.inl
noncomputable def rightPart (v : V) (j : ℕ) : Finset (LocalVertex G v j) := Finset.univ.image Sum.inr

theorem incidence_bipartite (v : V) (j : ℕ) :
    (incidenceGraph G v j).IsBipartiteWith (leftPart G v j : Set _) (rightPart G v j : Set _) := by
  classical
  constructor
  · apply Set.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨w,_,he⟩ := Finset.mem_image.mp hz'
    cases he
  · intro a b hab
    cases a <;> cases b
    · exact False.elim hab
    · left; simp [leftPart,rightPart]
    · right; simp [leftPart,rightPart]
    · exact False.elim hab

theorem incidence_edge_count (v : V) (j : ℕ) :
    (incidenceGraph G v j).edgeFinset.card = ∑ w ∈ layer G v j, codegree G v w := by
  classical
  have hh := (incidenceGraph G v j).isBipartiteWith_sum_degrees_eq_card_edges'
    (incidence_bipartite G v j)
  rw [rightPart, Finset.sum_image (fun _ _ _ _ h => Sum.inr.inj h)] at hh
  simp only [right_degree] at hh
  exact hh.symm.trans (Finset.sum_coe_sort _ _)

theorem incidence_order (v : V) (j : ℕ) :
    Fintype.card (LocalVertex G v j) = G.degree v + (layer G v j).card := by
  simp only [LocalVertex, Fintype.card_sum, Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree]

theorem layer_card_le_mass (v : V) (j : ℕ) (hj : 1 ≤ j) (Δ : ℕ)
    (hmax : ∀ x, G.degree x ≤ Δ) : (layer G v j).card ≤ G.degree v * Δ := by
  have ht := CodegreeLayerCake.threshold_incidence_le_mass (Finset.univ.erase v) (codegree G v) j
  have hm := offdiag_common_mass_le G v Δ hmax
  have hc : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hh := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (layer G v j).card : (0 : ℝ) ≤ (layer G v j).card)
  have he : CodegreeLayerCake.mass (Finset.univ.erase v) (codegree G v) =
      ∑ w ∈ Finset.univ.erase v, (Fintype.card (G.commonNeighbors v w) : ℝ) := rfl
  rw [he] at ht
  change (j : ℝ)*((layer G v j).card : ℝ) ≤ _ at ht
  have hb : ((layer G v j).card : ℝ) ≤ (G.degree v : ℝ)*(Δ : ℝ) := by nlinarith only [hh,ht,hm]
  exact_mod_cast hb

theorem incidence_order_le (v : V) (j : ℕ) (hj : 1 ≤ j) (Δ : ℕ)
    (hmax : ∀ x, G.degree x ≤ Δ) : Fintype.card (LocalVertex G v j) ≤ Δ+Δ^2 := by
  rw [incidence_order]
  have hh := layer_card_le_mass G v j hj Δ hmax
  nlinarith [hmax v]

/-- Authentic all-graph avoiding P8 input, not a threshold-density hypothesis. -/
theorem threshold_density_from_P8 (C : ℝ)
    (hP8 : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], ¬ HasRichCycle H →
      (H.edgeFinset.card : ℝ) ≤ C*(Fintype.card W : ℝ)*Real.log (2*(Fintype.card W : ℝ))^8)
    (havoid : ¬ HasRichCycle G) (hbip : G.IsBipartite) (v : V) (j : ℕ) (hj : 1 ≤ j) :
    (∑ w ∈ layer G v j, (codegree G v w : ℝ)) ≤
      C*((G.degree v : ℝ)+((layer G v j).card : ℝ))*
        Real.log (2*((G.degree v : ℝ)+((layer G v j).card : ℝ)))^8 := by
  classical
  have ha : ¬ HasRichCycle (incidenceGraph G v j) :=
    not_hasRichCycle_of_injective_hom (incidenceHom G v j)
      (incidenceHom_injective G hbip v j hj) havoid
  have hh := hP8 (LocalVertex G v j) (incidenceGraph G v j) ha
  rw [incidence_edge_count, incidence_order] at hh
  push_cast at hh
  exact hh
end Erdos642.CampaignFe72210bContinuation3.LocalCodegreeSubgraph
