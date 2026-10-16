import Openmath.Proofs.PaperSupport.B5MainDefs

/-! Original-edge thinning, support transport, small-order floors and the
literal Subgraph bridge used internally by the bare B5 assembly. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.B5
open QB4
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma ec_le_product (X Y : Finset V) : ec G X Y ≤ #X * #Y := by
  unfold ec
  calc _ ≤ ∑ _x ∈ X, #Y := sum_le_sum fun x _ => dg_le_card Y x
    _ = _ := by simp [sum_const, smul_eq_mul]

lemma fifteen_le_of_dense {U W : Finset V} (hn : 10 ≤ #U + #W)
    (he : 4 * (#U + #W) ≤ ec G U W + 5) : 15 ≤ #U + #W := by
  by_contra! hsmall
  have hp := ec_le_product (G := G) U W
  zify at hn he hsmall hp
  have hs := sq_nonneg ((#U : ℤ) - #W)
  have hi : (((#U : ℤ) + #W) - 10) * (((#U : ℤ) + #W) - 14) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  nlinarith

lemma small_potential_eight {X Y : Finset V} (hn : 3 ≤ #X + #Y)
    (hsmall : #X + #Y ≤ 9) : 12 ≤ potential 8 G X Y := by
  have hp := ec_le_product (G := G) X Y
  zify at hn hsmall hp
  have hs := sq_nonneg ((#X : ℤ) - #Y)
  have hi : (((#X : ℤ) + #Y) - 3) * (((#X : ℤ) + #Y) - 9) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  unfold potential
  nlinarith

lemma RegularPairs.mono_sets {q : ℕ} {X Y U W : Finset V}
    (hX : X ⊆ U) (hY : Y ⊆ W) (h : RegularPairs q G X Y) : RegularPairs q G U W := by
  obtain ⟨F, hne, hF, hadj, hU, hW⟩ := h
  exact ⟨F, hne, hF.trans (product_subset_product hX hY), hadj, hU, hW⟩

lemma RegularPairs.mono_graph {q : ℕ} {K : SimpleGraph V} {U W : Finset V}
    (hKG : K ≤ G) (h : RegularPairs q K U W) : RegularPairs q G U W := by
  obtain ⟨F, hne, hF, hadj, hU, hW⟩ := h
  exact ⟨F, hne, hF, fun x hx => hKG (hadj x hx), hU, hW⟩

lemma RegularPairs.swap {q : ℕ} {U W : Finset V} (h : RegularPairs q G U W) :
    RegularPairs q G W U := by
  obtain ⟨F, hne, hF, hadj, hU, hW⟩ := h
  refine ⟨F.map ⟨Prod.swap, Prod.swap_injective⟩, ?_, ?_, ?_, fun w => ?_, fun u => ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨_, mem_map_of_mem _ hx⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    obtain ⟨hyU, hyW⟩ := mem_product.mp (hF hy)
    exact mem_product.mpr ⟨hyW, hyU⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact (hadj y hy).symm
  · rw [filter_map, card_map]
    exact hW w
  · rw [filter_map, card_map]
    exact hU u

lemma FactorOn.regular_pairs {q : ℕ} {U W : Finset V}
    (hq : 0 < q) (hU : U.Nonempty) (h : FactorOn q G U W) : RegularPairs q G U W := by
  obtain ⟨F, hF, hadj, hP, hQ⟩ := h
  refine ⟨F, ?_, hF, hadj, fun u => ?_, fun w => ?_⟩
  · obtain ⟨u, hu⟩ := hU
    obtain ⟨x, hx⟩ := card_pos.mp (by rw [hP u hu]; exact hq)
    exact ⟨x, (mem_filter.mp hx).1⟩
  · by_cases hu : u ∈ U
    · exact Or.inr (hP u hu)
    · refine Or.inl (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun x hx hxu => hu ?_))
      rw [← hxu]
      exact (mem_product.mp (hF hx)).1
  · by_cases hw : w ∈ W
    · exact Or.inr (hQ w hw)
    · refine Or.inl (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun x hx hxw => hw ?_))
      rw [← hxw]
      exact (mem_product.mp (hF hx)).2

lemma dg_mono_graph {K : SimpleGraph V} [DecidableRel K.Adj]
    (hKG : K ≤ G) (S : Finset V) (a : V) : dg K S a ≤ dg G S a := by
  refine card_le_card fun w hw => ?_
  exact mem_filter.mpr ⟨(mem_filter.mp hw).1, hKG (mem_filter.mp hw).2⟩

open scoped Classical in
/-- Exact original edge thinning; the same original vertex type is retained. -/
theorem thin_pair {U W : Finset V} (hUW : Disjoint U W) (m : ℕ)
    (hm : m ≤ ec G U W) : ThinContract (G := G) U W m := by
  classical
  have hmc : m ≤ #(adjPairs G U W) := by simpa only [card_adjPairs] using hm
  obtain ⟨F, hF, hFm⟩ := exists_subset_card_eq hmc
  have hadj : ∀ x ∈ F, G.Adj x.1 x.2 := fun x hx => (mem_filter.mp (hF hx)).2
  have hFU : ∀ x ∈ F, x.1 ∈ U := fun x hx => (mem_product.mp (mem_filter.mp (hF hx)).1).1
  have hFW : ∀ x ∈ F, x.2 ∈ W := fun x hx => (mem_product.mp (mem_filter.mp (hF hx)).1).2
  let H := pairSubgraph F hadj
  let K := H.spanningCoe
  have hKG : K ≤ G := fun _ _ h => H.adj_sub h
  have hd : ∀ u ∈ U, dg K W u = #{x ∈ F | x.1 = u} := by
    intro u hu
    have huW : u ∉ W := disjoint_left.mp hUW hu
    have hf : {w ∈ W | K.Adj u w} = (F.filter fun x => x.1 = u).image Prod.snd := by
      ext w
      constructor
      · intro hw
        obtain ⟨hwW, hwadj⟩ := mem_filter.mp hw
        change ∃ x ∈ F, (x.1 = u ∧ x.2 = w) ∨ (x.1 = w ∧ x.2 = u) at hwadj
        obtain ⟨x, hx, hxuw | hxwu⟩ := hwadj
        · exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, hxuw.1⟩, hxuw.2⟩
        · exact (huW (hxwu.2 ▸ hFW x hx)).elim
      · intro hw
        obtain ⟨x, hx, hxw⟩ := mem_image.mp hw
        obtain ⟨hxF, hxu⟩ := mem_filter.mp hx
        refine mem_filter.mpr ⟨hxw ▸ hFW x hxF, ?_⟩
        change ∃ y ∈ F, (y.1 = u ∧ y.2 = w) ∨ (y.1 = w ∧ y.2 = u)
        exact ⟨x, hxF, Or.inl ⟨hxu, hxw⟩⟩
    unfold dg
    rw [hf]
    refine card_image_of_injOn fun x hx y hy hxy => ?_
    rw [mem_coe, mem_filter] at hx hy
    exact Prod.ext (hx.2.trans hy.2.symm) hxy
  refine ⟨K, hKG, ?_⟩
  calc ec K U W = ∑ u ∈ U, #{x ∈ F | x.1 = u} := sum_congr rfl hd
    _ = #F := (card_eq_sum_card_fiberwise hFU).symm
    _ = m := hFm

open scoped Classical in
theorem exists_subgraph_of_regularPairs [Fintype V] {q : ℕ} {U W : Finset V}
    (hUW : Disjoint U W) (h : RegularPairs q G U W) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  obtain ⟨F, hne, hF, hadj, hU, hW⟩ := h
  have hFU : ∀ x ∈ F, x.1 ∈ U := fun x hx => (mem_product.mp (hF hx)).1
  have hFW : ∀ x ∈ F, x.2 ∈ W := fun x hx => (mem_product.mp (hF hx)).2
  let H := pairSubgraph F hadj
  have hdeg : ∀ v ∈ H.verts, ∀ [Fintype (H.neighborSet v)], H.degree v = q := by
    rintro v ⟨x, hx, rfl | rfl⟩ _
    · rw [degree_pairSubgraph_left hadj hFW (disjoint_left.mp hUW (hFU x hx))]
      exact (hU x.1).resolve_left (card_ne_zero.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩)
    · rw [degree_pairSubgraph_right hadj hFU (disjoint_right.mp hUW (hFW x hx))]
      exact (hW x.2).resolve_left (card_ne_zero.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩)
  refine ⟨H, ?_, fun v => ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x.1, x, hx, Or.inl rfl⟩
  · rw [SimpleGraph.Subgraph.coe_degree]
    exact hdeg v v.2

#print axioms thin_pair
#print axioms exists_subgraph_of_regularPairs
end Erdos585.B5
