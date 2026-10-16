import Openmath.Proofs.PaperSupport.B5SelectorCore
import Openmath.Proofs.PaperSupport.B5Factor

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.B5
open QB4 B5Factor
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma potential_erase_left (D : ℤ) {X : Finset V} {a : V} (ha : a ∈ X) (T : Finset V) :
    potential D G (X.erase a) T = potential D G X T - D + 2 * (dg G T a : ℤ) := by
  have he : ec G (X.erase a) T + dg G T a = ec G X T := sum_erase_add X _ ha
  have hc := card_erase_add_one ha
  zify at he hc
  simp only [potential]
  rw [hc.symm, he.symm]
  ring

lemma FactorOn.swap {q : ℕ} {U W : Finset V} (h : FactorOn q G U W) :
    FactorOn q G W U := by
  obtain ⟨F, hF, hadj, hU, hW⟩ := h
  refine ⟨F.map ⟨Prod.swap, Prod.swap_injective⟩, ?_, ?_, fun w hw => ?_, fun u hu => ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    obtain ⟨hyU, hyW⟩ := mem_product.mp (hF hy)
    exact mem_product.mpr ⟨hyW, hyU⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact (hadj y hy).symm
  · rw [filter_map, card_map]
    exact hW w hw
  · rw [filter_map, card_map]
    exact hU u hu

/-- Original selected edges from one original port paying all actual cuts. -/
theorem factor_of_uncovered (q : ℕ) {U W : Finset V} {w : V}
    (hcard : #W = #U + 1) (hw : w ∈ W)
    (hgood : ∀ T ⊆ W, w ∈ T → theta q G U W T ≤ 0) :
    FactorOn q G U (W.erase w) := by
  have hcut : ∀ A ⊆ W.erase w, ∀ C ⊆ U,
      q * #A ≤ ec G A (U \ C) + q * #C := by
    intro A hA C hC
    have hAW : A ⊆ W := hA.trans (erase_subset w W)
    have hwA : w ∉ A := fun ha => (mem_erase.mp (hA ha)).1 rfl
    have hwT : w ∈ W \ A := mem_sdiff.mpr ⟨hw, hwA⟩
    have hg := hgood (W \ A) sdiff_subset hwT
    have hm := mixed_le_theta (G := G) q (W := W) (T := W \ A)
      (sdiff_subset : U \ C ⊆ U)
    have hi := cut_mixed_identity (G := G) q hcard hAW hC
    rw [hi] at hm
    have hz : (q : ℤ) * #A ≤ (ec G A (U \ C) : ℤ) + q * #C := by nlinarith
    exact_mod_cast hz
  obtain ⟨F, hF, hadj, hW, hU⟩ := exists_target_factor (k := q) (W.erase w) U
    (by rw [card_erase_of_mem hw, hcard, Nat.add_sub_cancel]) hcut
  exact FactorOn.swap ⟨F, hF, hadj, hW, hU⟩

def IsMaxPositive (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W M : Finset V) : Prop :=
  M ⊆ W ∧ M.Nonempty ∧ 0 < theta q G U W M ∧
    ∀ N ⊆ W, M ⊆ N → M ≠ N → theta q G U W N ≤ 0

lemma exists_max_positive (q : ℕ) {U W T : Finset V}
    (hT : T ⊆ W) (hne : T.Nonempty) (hp : 0 < theta q G U W T) :
    ∃ M, IsMaxPositive q G U W M := by
  let F := W.powerset.filter fun M => M.Nonempty ∧ 0 < theta q G U W M
  have hF : F.Nonempty := ⟨T, mem_filter.mpr ⟨mem_powerset.mpr hT, hne, hp⟩⟩
  obtain ⟨M, hM, hmax⟩ := exists_max_image F Finset.card hF
  obtain ⟨hmW, hmne, hmpos⟩ := mem_filter.mp hM
  refine ⟨M, mem_powerset.mp hmW, hmne, hmpos, ?_⟩
  intro N hNW hMN hneMN
  by_contra! hnpos
  have hnF : N ∈ F := mem_filter.mpr
    ⟨mem_powerset.mpr hNW, hmne.mono hMN, hnpos⟩
  have hle := hmax N hnF
  have hlt : #M < #N := card_lt_card
    ⟨hMN, fun hNM => hneMN (Subset.antisymm hMN hNM)⟩
  omega

namespace R2Input
variable {q : ℕ} {U W : Finset V}

lemma deficient_in_canonical (hq : 5 ≤ q) (h : R2Input q G U W)
    {a : V} (ha : a ∈ U) (hothers : ∀ b ∈ U, b ≠ a → dg G W b = 2 * q - 2)
    {T : Finset V} (hT : T ⊆ W) (hne : T.Nonempty) (hp : 0 < theta q G U W T) :
    a ∈ canonical q G U W T := by
  have hs := h.positive_shape hq hT hne hp
  by_contra haa
  have hz : deficiency (2 * (q : ℤ) - 2) G W (canonical q G U W T) = 0 := by
    refine sum_eq_zero fun b hb => ?_
    have hbu := canonical_subset q U W T hb
    have hba : b ≠ a := fun heq => haa (heq ▸ hb)
    have hd := hothers b hbu hba
    omega
  have hh := hs.2.2.2.2.1
  omega

/- -/
lemma positive_uses_neighbors (hq : 5 ≤ q) (h : R2Input q G U W)
    {a : V} (ha : a ∈ U) (hothers : ∀ b ∈ U, b ≠ a → dg G W b = 2 * q - 2)
    {T : Finset V} (hT : T ⊆ W) (hne : T.Nonempty) (hp : 0 < theta q G U W T) :
    q - 1 ≤ dg G T a := by
  have hs := h.positive_shape hq hT hne hp
  have hac := h.deficient_in_canonical hq ha hothers hT hne hp
  have hC : canonical q G U W T ⊆ U := canonical_subset q U W T
  have he := card_erase_of_mem hac
  have hcc := card_le_card hC
  have hsp := h.sparse ((canonical q G U W T).erase a)
    ((erase_subset _ _).trans hC) T hT (by omega) (by omega)
  have hid := potential_erase_left (G := G) (2 * (q : ℤ) - 2) hac T
  have hgp := hs.2.2.2.2.2
  rw [hid, hgp] at hsp
  omega

lemma positive_subset_max (hq : 5 ≤ q) (h : R2Input q G U W)
    {M T : Finset V} (hM : IsMaxPositive q G U W M)
    (hT : T ⊆ W) (hne : T.Nonempty) (hp : 0 < theta q G U W T) : T ⊆ M := by
  by_contra hnot
  have hMW := hM.1
  have hmne := hM.2.1
  have hmpos := hM.2.2.1
  have hU : M ∪ T ⊆ W := union_subset hMW hT
  have hneU : M ≠ M ∪ T := by
    intro heq
    apply hnot
    simpa only [← heq] using (subset_union_right : T ⊆ M ∪ T)
  have hthetaU := hM.2.2.2 (M ∪ T) hU subset_union_left hneU
  have hmt := (h.positive_shape hq hMW hmne hmpos).2.2.1
  have htt := (h.positive_shape hq hT hne hp).2.2.1
  have hdis : Disjoint M T := by
    refine disjoint_left.mpr fun a ham hat => ?_
    have hi : (M ∩ T).Nonempty := ⟨a, mem_inter.mpr ⟨ham, hat⟩⟩
    have hh := h.theta_nonempty_le_one hq (inter_subset_left.trans hMW) hi
    have hsuper := theta_supermod (G := G) q U W M T
    omega
  obtain ⟨a, ha, had, hothers⟩ := h.unique_deficient hq
  have hm := h.positive_uses_neighbors hq ha hothers hMW hmne hmpos
  have ht := h.positive_uses_neighbors hq ha hothers hT hne hp
  have hd := dg_union_of_disjoint (G := G) hdis a
  have hc := dg_mono (G := G) hU a
  omega

/-- A single actual original vertex pays ALL original omission cuts. -/
theorem uncovered (hq : 5 ≤ q) (h : R2Input q G U W) :
    ∃ w ∈ W, ∀ T ⊆ W, w ∈ T → theta q G U W T ≤ 0 := by
  have hwne : W.Nonempty := card_pos.mp (by have hc := h.card; omega)
  by_cases hex : ∃ T ⊆ W, T.Nonempty ∧ 0 < theta q G U W T
  · obtain ⟨T, hT, htne, htpos⟩ := hex
    obtain ⟨M, hM⟩ := exists_max_positive q hT htne htpos
    have hs := h.positive_shape hq hM.1 hM.2.1 hM.2.2.1
    have hout : ∃ w ∈ W, w ∉ M := by
      by_contra! hcover
      have hcard := card_le_card hcover
      omega
    obtain ⟨w, hw, hwM⟩ := hout
    refine ⟨w, hw, fun S hS hwS => ?_⟩
    by_contra! hsp
    have hsn : S.Nonempty := ⟨w, hwS⟩
    exact hwM (h.positive_subset_max hq hM hS hsn hsp hwS)
  · obtain ⟨w, hw⟩ := hwne
    refine ⟨w, hw, fun T hT hwT => ?_⟩
    by_contra! hp
    exact hex ⟨T, hT, ⟨w, hwT⟩, hp⟩

end R2Input

/- -/
theorem r2_original : R2Claim (G := G) := by
  intro q hq U W h
  obtain ⟨w, hw, hgood⟩ := h.uncovered hq
  exact ⟨w, hw, factor_of_uncovered q h.card hw hgood⟩

#print axioms R2Input.positive_uses_neighbors
#print axioms R2Input.uncovered
#print axioms r2_original
end Erdos585.B5
