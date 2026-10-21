import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CutExtractSubtype

/-! The actual union of edge-disjoint matchings restricted to a common right shore. -/
namespace Erdos642.CampaignFe72210bContinuation3.MatchingUnion
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (A B : Finset V) (hAB : Disjoint A B) (t : ℕ)
variable (partner : Fin t → ↥(B : Set V) → ↥(A : Set V))

/-- Exactly the supplied matching edges, with their two possible orientations. -/
def unionGraph : SimpleGraph V where
  Adj x y := (∃ i b, x = (partner i b).val ∧ y = b.val) ∨
    (∃ i b, y = (partner i b).val ∧ x = b.val)
  symm := ⟨by intro x y h; exact h.elim Or.inr Or.inl⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨i, b, hx, hb⟩ | ⟨i, b, hx, hb⟩ <;>
      exact Finset.disjoint_left.mp hAB
        (hx.symm ▸ (partner i b).property) (hb.symm ▸ b.property)⟩

noncomputable instance unionGraphDecidableRel :
    DecidableRel (unionGraph A B hAB t partner).Adj := Classical.decRel _

omit [Fintype V] [DecidableEq V] in
theorem unionGraph_isBipartiteWith :
    (unionGraph A B hAB t partner).IsBipartiteWith (A : Set V) (B : Set V) := by
  refine ⟨Finset.disjoint_coe.mpr hAB, ?_⟩
  intro x y h
  rcases h with ⟨i, b, hx, hy⟩ | ⟨i, b, hy, hx⟩
  · exact Or.inl ⟨hx.symm ▸ (partner i b).property, hy.symm ▸ b.property⟩
  · exact Or.inr ⟨hx.symm ▸ b.property, hy.symm ▸ (partner i b).property⟩

omit [Fintype V] in
theorem unionGraph_support :
    (unionGraph A B hAB t partner).support ⊆ (A ∪ B : Finset V) := by
  intro x hx
  obtain ⟨y, hxy⟩ := hx
  rcases (unionGraph_isBipartiteWith A B hAB t partner).mem_of_adj hxy with h | h
  · exact Finset.mem_union.mpr (Or.inl h.1)
  · exact Finset.mem_union.mpr (Or.inr h.1)

omit [Fintype V] [DecidableEq V] in
theorem adj_right_iff (b : (B : Set V)) (v : V) :
    (unionGraph A B hAB t partner).Adj b.val v ↔ ∃ i, v = (partner i b).val := by
  constructor
  · intro h
    rcases h with ⟨i, c, hb, hv⟩ | ⟨i, c, hv, hb⟩
    · exact False.elim (Finset.disjoint_left.mp hAB
        (hb.symm ▸ (partner i c).property) b.property)
    · have hc : c = b := Subtype.ext hb.symm
      subst c
      exact ⟨i, hv⟩
  · rintro ⟨i, hv⟩
    exact Or.inr ⟨i, b, hv, rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem adj_left_iff (a : (A : Set V)) (v : V) :
    (unionGraph A B hAB t partner).Adj a.val v ↔
      ∃ i b, v = b.val ∧ (partner i b).val = a.val := by
  constructor
  · intro h
    rcases h with ⟨i, b, ha, hv⟩ | ⟨i, b, hv, ha⟩
    · exact ⟨i, b, hv, ha.symm⟩
    · exact False.elim (Finset.disjoint_left.mp hAB a.property (ha.symm ▸ b.property))
  · rintro ⟨i, b, hv, ha⟩
    exact Or.inl ⟨i, b, ha.symm, hv⟩

theorem right_degree
    (hseparate : ∀ b, Function.Injective (fun i => (partner i b).val))
    (b : (B : Set V)) : (unionGraph A B hAB t partner).degree b.val = t := by
  classical
  let U := unionGraph A B hAB t partner
  have hneighbors : U.neighborFinset b.val =
      Finset.univ.image (fun i => (partner i b).val) := by
    ext v
    rw [U.mem_neighborFinset, adj_right_iff]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    simp only [eq_comm]
  rw [← U.card_neighborFinset_eq_degree, hneighbors,
    Finset.card_image_of_injective _ (hseparate b), Finset.card_univ, Fintype.card_fin]

omit [DecidableEq V] in
theorem left_degree_le (hinjective : ∀ i, Function.Injective (partner i))
    (a : (A : Set V)) : (unionGraph A B hAB t partner).degree a.val ≤ t := by
  classical
  let U := unionGraph A B hAB t partner
  have hwitness : ∀ v : U.neighborSet a.val,
      ∃ i b, v.val = b.val ∧ (partner i b).val = a.val := by
    intro v
    exact (adj_left_iff A B hAB t partner a v.val).mp v.property
  let f : U.neighborSet a.val → Fin t := fun v => (hwitness v).choose
  have hf : Function.Injective f := by
    intro v w hfw
    obtain ⟨b, hvb, hpb⟩ := (hwitness v).choose_spec
    obtain ⟨c, hwc, hpc⟩ := (hwitness w).choose_spec
    change (partner (f v) b).val = a.val at hpb
    change (partner (f w) c).val = a.val at hpc
    rw [← hfw] at hpc
    have hbc : b = c := hinjective (f v) (Subtype.ext (hpb.trans hpc.symm))
    apply Subtype.ext
    exact hvb.trans ((congrArg Subtype.val hbc).trans hwc.symm)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [U.card_neighborSet_eq_degree, Fintype.card_fin] using hc

theorem degree_le_of_mem_union
    (hinjective : ∀ i, Function.Injective (partner i))
    (hseparate : ∀ b, Function.Injective (fun i => (partner i b).val))
    (x : V) (hx : x ∈ A ∪ B) : (unionGraph A B hAB t partner).degree x ≤ t := by
  rcases Finset.mem_union.mp hx with ha | hb
  · exact left_degree_le A B hAB t partner hinjective ⟨x, ha⟩
  · exact (right_degree A B hAB t partner hseparate ⟨x, hb⟩).le

theorem edge_card (hseparate : ∀ b, Function.Injective (fun i => (partner i b).val)) :
    (unionGraph A B hAB t partner).edgeFinset.card = t * B.card := by
  classical
  have hh := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'
    (unionGraph_isBipartiteWith A B hAB t partner)
  have hs : (∑ b ∈ B, (unionGraph A B hAB t partner).degree b) = t * B.card := by
    calc
      _ = ∑ _b ∈ B, t := Finset.sum_congr rfl
        (fun b hb => right_degree A B hAB t partner hseparate ⟨b, hb⟩)
      _ = _ := by simp [Nat.mul_comm]
  exact hh.symm.trans hs

variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem unionGraph_le_original
    (hadj : ∀ i b, G.Adj (partner i b).val b.val) :
    unionGraph A B hAB t partner ≤ G := by
  intro x y h
  rcases h with ⟨i, b, hx, hy⟩ | ⟨i, b, hy, hx⟩
  · exact hx.symm ▸ hy.symm ▸ hadj i b
  · exact hx.symm ▸ hy.symm ▸ (hadj i b).symm

attribute [-instance] FinsetCoe.fintype in
omit [DecidableRel G.Adj] in
                                                                             
                                                                               
theorem typed_union_spec
    (hinjective : ∀ i, Function.Injective (partner i))
    (hseparate : ∀ b, Function.Injective (fun i => (partner i b).val))
    (hadj : ∀ i b, G.Adj (partner i b).val b.val)
    (hB : B.Nonempty) (hsize : A.card ≤ 2 * B.card) :
    let W := A ∪ B
    let H := (unionGraph A B hAB t partner).induce (W : Set V)
    (∀ x y : (W : Set V), H.Adj x y → G.Adj x.val y.val) ∧
    H.IsBipartite ∧
    Fintype.card (W : Set V) = A.card + B.card ∧
    Fintype.card (W : Set V) ≤ 3 * B.card ∧
    H.edgeFinset.card = t * B.card ∧
    (∀ x : (W : Set V), H.degree x ≤ t) ∧
    (∀ b : (B : Set V), H.degree ⟨b.val, Finset.mem_union.mpr (Or.inr b.property)⟩ = t) ∧
    (2 : ℝ) * t / 3 ≤ graphAverage H := by
  classical
  let W := A ∪ B
  let U := unionGraph A B hAB t partner
  let H := U.induce (W : Set V)
  have hs : U.support ⊆ (W : Set V) := unionGraph_support A B hAB t partner
  have hcard : Fintype.card (W : Set V) = A.card + B.card := by
    rw [Fintype.card_of_finset' W (fun _ => Iff.rfl)]
    exact Finset.card_union_of_disjoint hAB
  have horder : Fintype.card (W : Set V) ≤ 3 * B.card := by omega
  have hedge : H.edgeFinset.card = t * B.card :=
    (U.card_edgeFinset_induce_of_support_subset hs).trans (edge_card A B hAB t partner hseparate)
  have hdegree : ∀ x : (W : Set V), H.degree x ≤ t := by
    intro x
    rw [U.degree_induce_of_support_subset hs]
    exact degree_le_of_mem_union A B hAB t partner hinjective hseparate x.val x.property
  have hright : ∀ b : (B : Set V),
      H.degree ⟨b.val, Finset.mem_union.mpr (Or.inr b.property)⟩ = t := by
    intro b
    rw [U.degree_induce_of_support_subset hs]
    exact right_degree A B hAB t partner hseparate b
  have havg : (2 : ℝ) * t / 3 ≤ graphAverage H := by
    have hBpos : 0 < B.card := hB.card_pos
    have hcardpos : (0 : ℝ) < Fintype.card (W : Set V) := by exact_mod_cast (by omega : 0 < Fintype.card (W : Set V))
    have horderreal : (Fintype.card (W : Set V) : ℝ) ≤ 3 * (B.card : ℝ) := by exact_mod_cast horder
    unfold graphAverage
    rw [degreeVolume_eq_twice_edges, hedge]
    apply (le_div_iff₀ hcardpos).mpr
    calc
      (2 * (t : ℝ) / 3) * (Fintype.card (W : Set V) : ℝ) ≤
          (2 * (t : ℝ) / 3) * (3 * (B.card : ℝ)) :=
        mul_le_mul_of_nonneg_left horderreal (by positivity)
      _ = 2 * ((t * B.card : ℕ) : ℝ) := by push_cast; ring
  refine ⟨?_, ?_, hcard, horder, hedge, hdegree, hright, havg⟩
  · intro x y hxy
    exact unionGraph_le_original A B hAB t partner G hadj hxy
  · exact induce_isBipartite U W (unionGraph_isBipartiteWith A B hAB t partner).isBipartite

end Erdos642.CampaignFe72210bContinuation3.MatchingUnion
