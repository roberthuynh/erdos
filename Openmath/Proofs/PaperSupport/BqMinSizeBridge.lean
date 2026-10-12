import Openmath.Proofs.PaperSupport.BqMinSizeQuotas
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.BqMinimumSupport
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Transfer only the selected actual edges back to the original graph. -/
theorem factor_mono_graph {K : SimpleGraph V} {q : ℕ} {A B : Finset V}
    (hKG : K ≤ G) (h : FactorOn q K A B) : FactorOn q G A B := by
  obtain ⟨F,hF,hadj,hA,hB⟩ := h
  exact ⟨F,hF,fun x hx => hKG (hadj x hx),hA,hB⟩

open scoped Classical in
/-- Positive full quotas identify the entire retained vertex set exactly. -/
theorem factor_subgraph [Fintype V] {q : ℕ} {A B : Finset V}
    (hq : 0 < q) (hAB : Disjoint A B) (hcard : 0 < #A + #B)
    (h : FactorOn q G A B) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧
      H.verts.ncard = #A + #B := by
  classical
  obtain ⟨F,hF,hadj,hA,hB⟩ := h
  have hFA : ∀ x ∈ F, x.1 ∈ A := fun x hx => (mem_product.mp (hF hx)).1
  have hFB : ∀ x ∈ F, x.2 ∈ B := fun x hx => (mem_product.mp (hF hx)).2
  let H := pairSubgraph F hadj
  have hverts : H.verts = ↑(A ∪ B) := by
    ext v
    constructor
    · rintro ⟨x,hx,rfl | rfl⟩
      · exact mem_coe.mpr (mem_union_left B (hFA x hx))
      · exact mem_coe.mpr (mem_union_right A (hFB x hx))
    · intro hv
      rcases mem_union.mp (mem_coe.mp hv) with ha | hb
      · have hpos : 0 < #{x ∈ F | x.1 = v} := by rw [hA v ha];exact hq
        obtain ⟨x,hx⟩ := card_pos.mp hpos
        obtain ⟨hxF,hxv⟩ := mem_filter.mp hx
        exact ⟨x,hxF,Or.inl hxv⟩
      · have hpos : 0 < #{x ∈ F | x.2 = v} := by rw [hB v hb];exact hq
        obtain ⟨x,hx⟩ := card_pos.mp hpos
        obtain ⟨hxF,hxv⟩ := mem_filter.mp hx
        exact ⟨x,hxF,Or.inr hxv⟩
  have hdeg : ∀ v ∈ H.verts, ∀ [Fintype (H.neighborSet v)], H.degree v = q := by
    rintro v ⟨x,hx,rfl | rfl⟩ _
    · rw [degree_pairSubgraph_left hadj hFB (disjoint_left.mp hAB (hFA x hx))]
      exact hA x.1 (hFA x hx)
    · rw [degree_pairSubgraph_right hadj hFA (disjoint_right.mp hAB (hFB x hx))]
      exact hB x.2 (hFB x hx)
  refine ⟨H,?_,fun v => ?_,?_⟩
  · rw [hverts]
    obtain ⟨v,hv⟩ := card_pos.mp (show 0 < #(A ∪ B) by rw [card_union_of_disjoint hAB];exact hcard)
    exact ⟨v,mem_coe.mpr hv⟩
  · rw [SimpleGraph.Subgraph.coe_degree]
    exact hdeg v v.2
  · rw [hverts,Set.ncard_coe_finset,card_union_of_disjoint hAB]
end Erdos585.BqMinimumSupport
