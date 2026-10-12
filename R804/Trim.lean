import R804.Quota

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] r804DecidableEq
namespace Erdos585.R804
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q j ξ : ℕ} {A B AH BH : Finset V}

lemma exists_cleanup (q : ℕ) (A B : Finset V) : ∃ AH BH, Cleanup G q A B AH BH := by
  obtain ⟨AH,hAH,hAc⟩ := exists_subset_card_eq (Nat.min_le_left #(A\marked G q) #(B\marked G q))
  obtain ⟨BH,hBH,hBc⟩ := exists_subset_card_eq (Nat.min_le_right #(A\marked G q) #(B\marked G q))
  exact ⟨AH,BH,⟨hAH,hBH,by omega,hAc⟩⟩

lemma card_le_unmarked (P : Finset V) : #P≤#(P\marked G q)+#(marked G q) := by
  have hs : P⊆(P\marked G q)∪marked G q := by
    intro v hv
    by_cases he : v∈marked G q
    · exact mem_union_right _ he
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hv,he⟩)
  exact (card_le_card hs).trans (card_union_le _ _)

namespace Cleanup
variable (d : Cleanup G q A B AH BH)
include d

lemma left_original : AH⊆A := d.left.trans sdiff_subset
lemma right_original : BH⊆B := d.right.trans sdiff_subset

/-- Counts for EVERY balancing choice, not independently chosen omissions. -/
lemma omission_counts (hcard : #B=#A+j) :
    #(A\AH)≤#(marked G q) ∧ #(B\BH)=j+#(A\AH) := by
  have hs := card_sdiff_add_card_eq_card d.left_original
  have ho := card_sdiff_add_card_eq_card d.right_original
  have heq := d.balanced
  have ha := card_le_unmarked (G:=G) (q:=q) A
  have hb := card_le_unmarked (G:=G) (q:=q) B
  constructor
  · rcases le_total #(A\marked G q) #(B\marked G q) with hab | hba
    · have hm : #AH=#(A\marked G q) := by rw [d.size,Nat.min_eq_left hab]
      omega
    · have hm : #AH=#(B\marked G q) := by rw [d.size,Nat.min_eq_right hba]
      omega
  · omega

lemma omission_bounds (host : Host h q j ξ G A B) :
    #(A\AH)≤8*h-1 ∧ #(B\BH)=j+#(A\AH) ∧
    #(B\BH)≤8*h+j-1 ∧ #(B\BH)<9*h := by
  have hc := d.omission_counts host.card
  have he := Host.marked_card host
  have hn := Host.numeric host
  omega

lemma nonempty (host : Host h q j ξ G A B) {x : V} (hx : x∈A) : AH.Nonempty := by
  have hs := Host.shores_large host hx
  have hA := card_le_unmarked (G:=G) (q:=q) A
  have hB := card_le_unmarked (G:=G) (q:=q) B
  have he := Host.marked_card host
  have hn := Host.numeric host
  have ha : 0<#(A\marked G q) := by omega
  have hb : 0<#(B\marked G q) := by omega
  apply card_pos.mp
  rw [d.size]
  exact lt_min ha hb

lemma essential_deleted (host : Host h q j ξ G A B) {T I : Finset V}
    (hi : MinimalFailed G q j B T I) (hT : T⊆A) : I⊆A\AH := by
  intro v hv
  exact mem_sdiff.mpr ⟨hT (hi.subset hv),fun hh =>
    (mem_sdiff.mp (d.left hh)).2 (hi.marked host hv)⟩

lemma retained_left (host : Host h q j ξ G A B) {v : V} (hv : v∈AH) :
    13*q≤8*dg G BH v := by
  classical
  have hva := d.left_original hv
  have hnot := (mem_sdiff.mp (d.left hv)).2
  have hscar : 4*scar (G:=G) q v≤q := by
    by_contra! hb
    exact hnot ((mem_marked v).mpr hb)
  have he := Nat.sub_add_cancel (host.cap_degree v)
  have hdeg : dg G B v=G.degree v := dg_eq_degree host.bipartite hva
  have hsplit := dg_sdiff_add (G:=G) d.right_original v
  have hloss := dg_le_card (G:=G) (B\BH) v
  have ho := d.omission_bounds host
  have hn := Host.numeric host
  unfold scar at hscar
  omega

lemma retained_right (host : Host h q j ξ G A B) {v : V} (hv : v∈BH) :
    13*q≤8*dg G AH v := by
  classical
  have hvb := d.right_original hv
  have hnot := (mem_sdiff.mp (d.right hv)).2
  have hscar : 4*scar (G:=G) q v≤q := by
    by_contra! hb
    exact hnot ((mem_marked v).mpr hb)
  have he := Nat.sub_add_cancel (host.cap_degree v)
  have hdeg : dg G A v=G.degree v := dg_eq_degree host.bipartite.symm hvb
  have hsplit := dg_sdiff_add (G:=G) d.left_original v
  have hloss := dg_le_card (G:=G) (A\AH) v
  have ho := d.omission_bounds host
  have hn := Host.numeric host
  unfold scar at hscar
  omega

lemma shore_bounds (host : Host h q j ξ G A B) {T I : Finset V}
    {x : V} (hx : x∈A) (hi : MinimalFailed G q j B T I)
    (hT : T⊆A) (hTc : #T≤3) : q≤#AH ∧ 8*#AH≤25*q := by
  obtain ⟨v,hv⟩ := d.nonempty host hx
  have hd := d.retained_left host hv
  have hm := dg_le_card (G:=G) BH v
  have he := d.balanced
  have hu := hi.shore_bound host hT hTc
  have hc := card_le_card d.left_original
  have hn := Host.numeric host
  omega

end Cleanup
end Erdos585.R804
