import Openmath.Proofs.PaperSupport.QB6Assembly

/- 





-/

open Finset
namespace Erdos585.QB6C3S
open QB4 QB5 QB6Assembly

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def row (G : SimpleGraph V) [DecidableRel G.Adj] (W T : Finset V) (a : V) : ℤ :=
  (dg G T a : ℤ) - (dg G W a : ℤ) + 4

def capTheta (G : SimpleGraph V) [DecidableRel G.Adj] (U W T : Finset V) : ℤ :=
  4 - 4 * #T + ∑ a ∈ U, max 0 (row G W T a)

def canonical (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W T : Finset V) : Finset V :=
  U.filter fun a => 0 < row G W T a

def mixedTheta (G : SimpleGraph V) [DecidableRel G.Adj]
    (W X T : Finset V) : ℤ :=
  4 - 4 * #T + ∑ a ∈ X, row G W T a

omit [DecidableEq V] in
lemma canonical_subset (U W T : Finset V) : canonical G U W T ⊆ U := filter_subset _ _

omit [DecidableEq V] in
lemma mixed_le_cap {U W X T : Finset V} (hX : X ⊆ U) :
    mixedTheta G W X T ≤ capTheta G U W T := by
  unfold mixedTheta capTheta
  have h1 : (∑ a ∈ X, row G W T a) ≤ ∑ a ∈ X, max 0 (row G W T a) :=
    sum_le_sum fun a _ => le_max_right _ _
  have h2 : (∑ a ∈ X, max 0 (row G W T a)) ≤ ∑ a ∈ U, max 0 (row G W T a) :=
    sum_le_sum_of_subset_of_nonneg hX fun a _ _ => le_max_left _ _
  linarith

omit [DecidableEq V] in
lemma mixed_canonical (U W T : Finset V) :
    mixedTheta G W (canonical G U W T) T = capTheta G U W T := by
  have hsum : (∑ a ∈ canonical G U W T, row G W T a) =
      ∑ a ∈ U, max 0 (row G W T a) := by
    rw [canonical, sum_filter]
    apply sum_congr rfl
    intro a _
    split_ifs with h
    · exact (max_eq_right (le_of_lt h)).symm
    · exact (max_eq_left (le_of_not_gt h)).symm
  simp only [mixedTheta, capTheta, hsum]

omit [DecidableEq V] in
lemma row_sum (W X T : Finset V) :
    (∑ a ∈ X, row G W T a) =
      (ec G X T : ℤ) - (ec G X W : ℤ) + 4 * #X := by
  simp [row, sum_add_distrib, sum_sub_distrib, ec, Nat.cast_sum,
    sum_const, mul_comm]

omit [DecidableEq V] in
lemma mixed_potential (W X T : Finset V) :
    2 * mixedTheta G W X T =
      8 + 2 * ((#X : ℤ) - #T) + 2 * df G W X - gv G X T := by
  rw [mixedTheta, row_sum, df_eq]
  unfold gv
  ring

lemma cut_mixed_identity {U W A C : Finset V}
    (hcard : #W = #U + 1) (hA : A ⊆ W) (hC : C ⊆ U) :
    mixedTheta G W (U \ C) (W \ A) =
      4 * ((#A : ℤ) - #C) - (ec G A (U \ C) : ℤ) := by
  have hcA := card_sdiff_add_card_eq_card hA
  have hcC := card_sdiff_add_card_eq_card hC
  have he := ec_sdiff_add_right (G := G) hA (U \ C)
  have hecomm := ec_comm (G := G) (U \ C) A
  zify at hcard hcA hcC he hecomm
  rw [mixedTheta, row_sum]
  linarith

theorem quartic_of_uncovered {U W : Finset V} {w : V}
    (hcard : #W = #U + 1) (hU : U.Nonempty) (hw : w ∈ W)
    (hgood : ∀ T ⊆ W, w ∈ T → capTheta G U W T ≤ 0) :
    Quartic G U W := by
  have hcut : ∀ A ⊆ W.erase w, ∀ C ⊆ U,
      4 * #A ≤ ec G A (U \ C) + 4 * #C := by
    intro A hA C hC
    have hAW : A ⊆ W := hA.trans (erase_subset w W)
    have hwA : w ∉ A := fun h => (mem_erase.1 (hA h)).1 rfl
    have hwT : w ∈ W \ A := mem_sdiff.2 ⟨hw, hwA⟩
    have hc := hgood (W \ A) sdiff_subset hwT
    have hm := mixed_le_cap (G := G) (W := W) (T := W \ A)
      (sdiff_subset : U \ C ⊆ U)
    have hi := cut_mixed_identity (G := G) hcard hAW hC
    rw [hi] at hm
    omega
  obtain ⟨F, hF, hadj, hFP, hFQ⟩ := exists_four_factor (W.erase w) U
    (by rw [card_erase_of_mem hw, hcard, Nat.add_sub_cancel]) hcut
  exact quartic_of_four_factor (erase_subset w W) hU hF hadj hFP hFQ

namespace C3SInput

omit [DecidableEq V] in
lemma gv_full {U W : Finset V} (h : QB6Assembly.C3SInput G U W) : gv G U W = 12 := by
  have hg := gv_eq_right (G := G) U W
  have hc := h.card
  have hd := h.deficiency
  zify at hc
  omega

omit [DecidableEq V] in
lemma defW {U W : Finset V} (h : QB6Assembly.C3SInput G U W) : df G U W = 9 := by
  have h1 := df_right_eq (G := G) h.card
  have h2 := h.deficiency
  omega

omit [DecidableEq V] in
lemma nonempty_U {U W : Finset V} (h : QB6Assembly.C3SInput G U W) : U.Nonempty := by
  by_contra hu
  have hz : U = ∅ := not_nonempty_iff_eq_empty.mp hu
  have hwcard : #W = 1 := by rw [hz] at h; simpa using h.card
  obtain ⟨w, hw⟩ := card_pos.mp (by omega : 0 < #W)
  have hm := h.minW w hw
  rw [hz] at hm
  simp [dg] at hm

end C3SInput

theorem pospart_supermod (a b c d r : ℤ) (hs : a + b = c + d)
    (hca : c ≤ a) (hcb : c ≤ b) :
    max 0 (a-r) + max 0 (b-r) ≤ max 0 (c-r) + max 0 (d-r) := by
  omega

theorem cap_supermod (U W M N : Finset V) :
    capTheta G U W M + capTheta G U W N ≤
      capTheta G U W (M ∪ N) + capTheta G U W (M ∩ N) := by
  have hpoint : ∀ a ∈ U,
      max 0 (row G W M a) + max 0 (row G W N a) ≤
        max 0 (row G W (M ∪ N) a) + max 0 (row G W (M ∩ N) a) := by
    intro a _
    have hsum := dg_union_add_dg_inter (G := G) M N a
    have h1 := dg_mono (G := G) (inter_subset_left : M ∩ N ⊆ M) a
    have h2 := dg_mono (G := G) (inter_subset_right : M ∩ N ⊆ N) a
    zify at hsum h1 h2
    have hh := pospart_supermod (dg G M a) (dg G N a) (dg G (M ∩ N) a)
      (dg G (M ∪ N) a) ((dg G W a : ℤ)-4) (by omega) h1 h2
    simpa [row, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hh
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib, sum_add_distrib] at hsum
  have hcard := card_union_add_card_inter M N
  zify at hcard
  unfold capTheta
  linarith

omit [DecidableEq V] in
lemma canonical_mono {U W M N : Finset V} (h : M ⊆ N) :
    canonical G U W M ⊆ canonical G U W N := by
  intro a ha
  obtain ⟨haU, ha⟩ := mem_filter.mp ha
  have hm := dg_mono (G := G) h a
  refine mem_filter.mpr ⟨haU, ?_⟩
  unfold row at ha ⊢
  omega

namespace C3SInput

omit [DecidableEq V] in
lemma theta_empty {U W : Finset V} (h : QB6Assembly.C3SInput G U W) :
    capTheta G U W ∅ = 4 := by
  have hs : (∑ a ∈ U, max 0 (row G W ∅ a)) = 0 := by
    apply sum_eq_zero
    intro a ha
    have hm := h.minU a ha
    have hz : dg G ∅ a = 0 := by simp [dg]
    apply max_eq_left
    unfold row
    omega
  simp [capTheta, hs]

omit [DecidableEq V] in
lemma theta_full {U W : Finset V} (h : QB6Assembly.C3SInput G U W) :
    capTheta G U W W = 0 := by
  have hc := h.card
  have hs : (∑ a ∈ U, max 0 (row G W W a)) = 4 * #U := by
    simp [row, sum_const, mul_comm]
  unfold capTheta
  rw [hs]
  omega

omit [DecidableEq V] in
lemma theta_singleton_le {U W : Finset V} (h : QB6Assembly.C3SInput G U W) (w : V) :
    capTheta G U W {w} ≤ 1 := by
  have hp : ∀ a ∈ U, 2 * max 0 (row G W {w} a) ≤ 6 - (dg G W a : ℤ) := by
    intro a ha
    have hm := h.minU a ha
    have hb := h.capU a ha
    have hs : dg G {w} a ≤ 1 := by simpa using dg_le_card (G := G) {w} a
    unfold row
    omega
  have hsum := sum_le_sum hp
  rw [← mul_sum] at hsum
  change 2 * (∑ a ∈ U, max 0 (row G W {w} a)) ≤ df G W U at hsum
  have hd := h.deficiency
  simp only [capTheta, card_singleton]
  omega

omit [DecidableEq V] in
lemma theta_two_le {U W T : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hT : #T = 2) : capTheta G U W T ≤ -1 := by
  have hp : ∀ a ∈ U, max 0 (row G W T a) ≤ 6 - (dg G W a : ℤ) := by
    intro a ha
    have hm := h.minU a ha
    have hb := h.capU a ha
    have hs : dg G T a ≤ 2 := (dg_le_card (G := G) T a).trans_eq hT
    unfold row
    omega
  have hsum := sum_le_sum hp
  change (∑ a ∈ U, max 0 (row G W T a)) ≤ df G W U at hsum
  have hd := h.deficiency
  simp only [capTheta, hT]
  omega

omit [DecidableEq V] in
lemma canonical_potential {U W T : Finset V} :
    2 * capTheta G U W T =
      8 + 2 * ((#(canonical G U W T) : ℤ) - #T) +
        2 * df G W (canonical G U W T) - gv G (canonical G U W T) T := by
  have hh := mixed_potential (G := G) W (canonical G U W T) T
  rwa [mixed_canonical] at hh

lemma canonical_bounds {U W T : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hT : T ⊆ W) (hlt : #T < #W) (h3 : 3 ≤ #T) :
    14 ≤ gv G (canonical G U W T) T ∧
      0 ≤ df G W (canonical G U W T) ∧ df G W (canonical G U W T) ≤ 3 ∧
      6 * ((#(canonical G U W T) : ℤ)-#T) ≤ gv G (canonical G U W T) T ∧
      6 * ((#T : ℤ)-#(canonical G U W T)) ≤ gv G (canonical G U W T) T := by
  have hX := canonical_subset (G := G) U W T
  have hcx := card_le_card hX
  have hd0 := df_nonneg (G := G) fun a ha => h.capU a (hX ha)
  have hd3 := df_le_of_subset (G := G) hX h.capU
  have hg := h.sparse (canonical G U W T) hX T hT (by omega) (by omega)
  have hdfT := df_nonneg (G := G) fun y hy =>
    (dg_mono (G := G) hX y).trans (h.capW y (hT hy))
  have hdfX := df_nonneg (G := G) fun x hx =>
    (dg_mono (G := G) hT x).trans (h.capU x (hX hx))
  have hgl := gv_eq_left (G := G) (canonical G U W T) T
  have hgr := gv_eq_right (G := G) (canonical G U W T) T
  have hdef := h.deficiency
  refine ⟨hg, hd0, by omega, ?_, ?_⟩ <;> omega

lemma theta_large_le {U W T : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hT : T ⊆ W) (hlt : #T < #W) (h3 : 3 ≤ #T) : capTheta G U W T ≤ 2 := by
  obtain ⟨hg, hd0, hd3, hk1, hk2⟩ := canonical_bounds h hT hlt h3
  have ht := canonical_potential (G := G) (U := U) (W := W) (T := T)
  omega

lemma theta_nonempty_le {U W T : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hT : T ⊆ W) (hne : T.Nonempty) : capTheta G U W T ≤ 2 := by
  by_cases heq : T = W
  · rw [heq, theta_full h]
    omega
  have hlt : #T < #W := card_lt_card ⟨hT, fun hh => heq (Subset.antisymm hT hh)⟩
  have hpos := card_pos.mpr hne
  rcases (by omega : #T = 1 ∨ #T = 2 ∨ 3 ≤ #T) with h1 | h2 | h3
  · obtain ⟨w, hw⟩ := card_eq_one.mp h1
    rw [hw]
    exact (theta_singleton_le h w).trans (by norm_num)
  · exact (theta_two_le h h2).trans (by norm_num)
  · exact theta_large_le h hT hlt h3

end C3SInput

def PositiveSignature (k g d t : ℤ) : Prop :=
  (k = 1 ∧ g = 14 ∧ d = 3 ∧ t = 1) ∨
  (k = 2 ∧ g = 16 ∧ d = 3 ∧ t = 1) ∨
  (k = 2 ∧ g = 14 ∧ d = 2 ∧ t = 1) ∨
  (k = 2 ∧ g = 14 ∧ d = 3 ∧ t = 2) ∨
  (k = 3 ∧ g = 18 ∧ d = 3 ∧ t = 1)

theorem positive_signature_scalar {k g d t : ℤ} (hg : 14 ≤ g)
    (hd0 : 0 ≤ d) (hd3 : d ≤ 3) (hk1 : 6*k ≤ g) (hk2 : -6*k ≤ g)
    (ht : 2*t = 8+2*k+2*d-g) (hpos : 1 ≤ t) : PositiveSignature k g d t := by
  unfold PositiveSignature
  omega

theorem positive_signature {U W T : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hT : T ⊆ W) (hlt : #T < #W) (h3 : 3 ≤ #T) (hpos : 1 ≤ capTheta G U W T) :
    PositiveSignature ((#(canonical G U W T) : ℤ)-#T)
      (gv G (canonical G U W T) T) (df G W (canonical G U W T)) (capTheta G U W T) := by
  obtain ⟨hg, hd0, hd3, hk1, hk2⟩ := C3SInput.canonical_bounds h hT hlt h3
  exact positive_signature_scalar hg hd0 hd3 hk1 (by linarith)
    (C3SInput.canonical_potential (G := G)) hpos

namespace FiniteTests

variable (f : Finset V → ℤ)

def IsMaxPositive (W M : Finset V) : Prop :=
  M ⊆ W ∧ M.Nonempty ∧ 1 ≤ f M ∧
    ∀ N ⊆ W, M ⊆ N → 1 ≤ f N → N = M

def IsMaxTwo (W K : Finset V) : Prop :=
  K ⊆ W ∧ K.Nonempty ∧ 2 ≤ f K ∧
    ∀ N ⊆ W, K ⊆ N → 2 ≤ f N → N = K

def Supermodular : Prop := ∀ M N, f M + f N ≤ f (M ∪ N) + f (M ∩ N)

variable {f}

/-- Credited finite-maximum pattern: QB5.KL1Merge.exists_isMaxOver. -/
theorem exists_max_positive {W M : Finset V} (hM : M ⊆ W) (hne : M.Nonempty)
    (hpos : 1 ≤ f M) : ∃ N, M ⊆ N ∧ IsMaxPositive f W N := by
  classical
  obtain ⟨N, hN, hmax⟩ := exists_max_image
    (W.powerset.filter fun N => M ⊆ N ∧ 1 ≤ f N) card
    ⟨M, mem_filter.mpr ⟨mem_powerset.mpr hM, Subset.rfl, hpos⟩⟩
  obtain ⟨hNW, hMN, hNpos⟩ := (by simpa only [mem_filter, mem_powerset] using hN :
    N ⊆ W ∧ M ⊆ N ∧ 1 ≤ f N)
  refine ⟨N, hMN, hNW, hne.mono hMN, hNpos, ?_⟩
  intro L hL hNL hLpos
  have hc := hmax L (mem_filter.mpr ⟨mem_powerset.mpr hL, hMN.trans hNL, hLpos⟩)
  exact (eq_of_subset_of_card_le hNL hc).symm

theorem exists_max_two {W K : Finset V} (hK : K ⊆ W) (hne : K.Nonempty)
    (hpos : 2 ≤ f K) : ∃ N, K ⊆ N ∧ IsMaxTwo f W N := by
  classical
  obtain ⟨N, hN, hmax⟩ := exists_max_image
    (W.powerset.filter fun N => K ⊆ N ∧ 2 ≤ f N) card
    ⟨K, mem_filter.mpr ⟨mem_powerset.mpr hK, Subset.rfl, hpos⟩⟩
  obtain ⟨hNW, hKN, hNpos⟩ := (by simpa only [mem_filter, mem_powerset] using hN :
    N ⊆ W ∧ K ⊆ N ∧ 2 ≤ f N)
  refine ⟨N, hKN, hNW, hne.mono hKN, hNpos, ?_⟩
  intro L hL hNL hLpos
  have hc := hmax L (mem_filter.mpr ⟨mem_powerset.mpr hL, hKN.trans hNL, hLpos⟩)
  exact (eq_of_subset_of_card_le hNL hc).symm

theorem union_nonpositive {W M N : Finset V} (hM : IsMaxPositive f W M)
    (hN : IsMaxPositive f W N) (hne : M ≠ N) : f (M ∪ N) ≤ 0 := by
  by_contra hc
  have hp : 1 ≤ f (M ∪ N) := by omega
  have h1 := hM.2.2.2 (M ∪ N) (union_subset hM.1 hN.1) subset_union_left hp
  have h2 := hN.2.2.2 (M ∪ N) (union_subset hM.1 hN.1) subset_union_right hp
  exact hne (h1.symm.trans h2)

theorem disjoint_of_no_two {W M N : Finset V} (hs : Supermodular f)
    (hb : ∀ T ⊆ W, T.Nonempty → f T ≤ 1)
    (hM : IsMaxPositive f W M) (hN : IsMaxPositive f W N) (hne : M ≠ N) :
    Disjoint M N := by
  apply disjoint_left.mpr
  intro a haM haN
  have hi := hb (M ∩ N) (inter_subset_left.trans hM.1) ⟨a, mem_inter.mpr ⟨haM, haN⟩⟩
  have hu := union_nonpositive hM hN hne
  have hh := hs M N
  have hm := hM.2.2.1
  have hn := hN.2.2.1
  omega

theorem hub_subset {W M K : Finset V} (hs : Supermodular f)
    (hb : ∀ T ⊆ W, T.Nonempty → f T ≤ 2)
    (hM : IsMaxPositive f W M) (hK : IsMaxTwo f W K) (hi : (M ∩ K).Nonempty) :
    K ⊆ M := by
  have hib := hb (M ∩ K) (inter_subset_left.trans hM.1) hi
  have hh := hs M K
  have hm := hM.2.2.1
  have hk := hK.2.2.1
  have hu : 1 ≤ f (M ∪ K) := by omega
  have he := hM.2.2.2 (M ∪ K) (union_subset hM.1 hK.1) subset_union_left hu
  exact he ▸ (subset_union_right : K ⊆ M ∪ K)

theorem hub_intersection {W M N K : Finset V} (hs : Supermodular f)
    (hb : ∀ T ⊆ W, T.Nonempty → f T ≤ 2)
    (hM : IsMaxPositive f W M) (hN : IsMaxPositive f W N) (hK : IsMaxTwo f W K)
    (hKM : K ⊆ M) (hKN : K ⊆ N) (hne : M ≠ N) :
    M ∩ N = K ∧ f M = 1 ∧ f N = 1 ∧ f (M ∪ N) = 0 := by
  have hiK : K ⊆ M ∩ N := subset_inter hKM hKN
  have hiW : M ∩ N ⊆ W := inter_subset_left.trans hM.1
  have hiNe := hK.2.1.mono hiK
  have hib := hb (M ∩ N) hiW hiNe
  have hu := union_nonpositive hM hN hne
  have hh := hs M N
  have hm := hM.2.2.1
  have hn := hN.2.2.1
  have hi2 : 2 ≤ f (M ∩ N) := by omega
  have heq := hK.2.2.2 (M ∩ N) hiW hiK hi2
  exact ⟨heq, by omega, by omega, by omega⟩

end FiniteTests

def weightedDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W T : Finset V) : ℤ :=
  ∑ a ∈ U, (6-(dg G W a : ℤ)) * (dg G T a : ℤ)

namespace C3SInput

lemma canonical_internal {U W T : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hT : T ⊆ W) (hlt : #T < #W) (h3 : 3 ≤ #T) {a : V}
    (ha : a ∈ canonical G U W T) :
    20 ≤ gv G (canonical G U W T) T + 2 * (dg G T a : ℤ) := by
  have hX := canonical_subset (G := G) U W T
  have hcx := card_le_card hX
  have hc := card_erase_add_one ha
  have hg := h.sparse ((canonical G U W T).erase a)
    ((erase_subset a _).trans hX) T hT (by omega) (by omega)
  have he := gv_erase_left (G := G) ha T
  omega

omit [DecidableEq V] in
lemma weighted_nonneg {U W T : Finset V} (h : QB6Assembly.C3SInput G U W) :
    0 ≤ weightedDegree G U W T := by
  apply sum_nonneg
  intro a ha
  have hc := h.capU a ha
  apply mul_nonneg
  · omega
  · exact Nat.cast_nonneg _

omit [DecidableEq V] in
lemma weighted_lower {U W X T : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hX : X ⊆ U) (n : ℕ) (hd : ∀ a ∈ X, n ≤ dg G T a) :
    (n : ℤ) * df G W X ≤ weightedDegree G U W T := by
  have h1 : (n : ℤ) * df G W X ≤
      ∑ a ∈ X, (6-(dg G W a : ℤ)) * (dg G T a : ℤ) := by
    unfold df
    rw [mul_sum]
    apply sum_le_sum
    intro a ha
    have hc := h.capU a (hX ha)
    have hl := hd a ha
    have hd0 : (0 : ℤ) ≤ 6-(dg G W a : ℤ) := by omega
    have hmul := mul_le_mul_of_nonneg_left (by exact_mod_cast hl : (n : ℤ) ≤ dg G T a) hd0
    simpa [mul_comm] using hmul
  have h2 : (∑ a ∈ X, (6-(dg G W a : ℤ)) * (dg G T a : ℤ)) ≤ weightedDegree G U W T := by
    apply sum_le_sum_of_subset_of_nonneg hX
    intro a ha _
    have hc := h.capU a ha
    exact mul_nonneg (by omega) (Nat.cast_nonneg _)
  exact h1.trans h2

lemma positive_weighted_bound {U W T : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hT : T ⊆ W) (hlt : #T < #W) (h3 : 3 ≤ #T) (hp : 1 ≤ capTheta G U W T) :
    9 * df G U T ≤ 4 * weightedDegree G U W T := by
  let X := canonical G U W T
  have hX : X ⊆ U := canonical_subset (G := G) U W T
  have hdf := df_anti (G := G) (Z := T) hX
  have hgv := gv_eq_left (G := G) X T
  have hw0 := weighted_nonneg (G := G) (T := T) h
  have hi : ∀ a ∈ X, 20 ≤ gv G X T + 2 * (dg G T a : ℤ) :=
    fun a ha => canonical_internal h hT hlt h3 ha
  have hs := positive_signature h hT hlt h3 hp
  change PositiveSignature ((#X : ℤ)-#T) (gv G X T) (df G W X) _ at hs
  rcases hs with hA | hB | hP | hH | hZ
  · obtain ⟨hk, hg, hd, _⟩ := hA
    have hl := weighted_lower (T := T) h hX 3 (fun a ha => by have := hi a ha; omega)
    omega
  · obtain ⟨hk, hg, hd, _⟩ := hB
    have hl := weighted_lower (T := T) h hX 2 (fun a ha => by have := hi a ha; omega)
    omega
  · obtain ⟨hk, hg, hd, _⟩ := hP
    have hl := weighted_lower (T := T) h hX 3 (fun a ha => by have := hi a ha; omega)
    omega
  · obtain ⟨hk, hg, hd, _⟩ := hH
    have hl := weighted_lower (T := T) h hX 3 (fun a ha => by have := hi a ha; omega)
    omega
  · obtain ⟨hk, hg, _, _⟩ := hZ
    omega

lemma erase_four_def {U W : Finset V} (h : QB6Assembly.C3SInput G U W) {a : V}
    (ha : a ∈ U) (hd : dg G W a = 4) : df G W (U.erase a) = 1 := by
  have hs := sum_erase_add U (fun x => (6 : ℤ)-dg G W x) ha
  change df G W (U.erase a) + (6-(dg G W a : ℤ)) = df G W U at hs
  have hu := h.deficiency
  rw [hd] at hs
  omega

lemma four_mem_of_def {U W X : Finset V} (h : QB6Assembly.C3SInput G U W) {a : V}
    (ha : a ∈ U) (hd : dg G W a = 4) (hX : X ⊆ U) (hdf : 2 ≤ df G W X) : a ∈ X := by
  by_contra hn
  have hXe : X ⊆ U.erase a := by
    intro x hx
    exact mem_erase.mpr ⟨fun he => hn (he ▸ hx), hX hx⟩
  have hm := df_le_of_subset (G := G) hXe (fun x hx => h.capU x (erase_subset a U hx))
  have he := erase_four_def h ha hd
  omega

lemma only_four {U W : Finset V} (h : QB6Assembly.C3SInput G U W) {a x : V}
    (ha : a ∈ U) (hd : dg G W a = 4) (hx : x ∈ U) (hxdeg : dg G W x = 4) : x = a := by
  by_contra hne
  have hxE : x ∈ U.erase a := mem_erase.mpr ⟨hne, hx⟩
  have hs := single_le_sum (f := fun y => (6 : ℤ)-dg G W y)
    (fun y hy => by have hc := h.capU y (erase_subset a U hy); omega) hxE
  change (6 : ℤ)-dg G W x ≤ df G W (U.erase a) at hs
  have he := erase_four_def h ha hd
  rw [hxdeg] at hs
  omega

lemma positive_singleton_four {U W : Finset V} (h : QB6Assembly.C3SInput G U W) {a w : V}
    (ha : a ∈ U) (hd : dg G W a = 4) (hp : 1 ≤ capTheta G U W {w}) : dg G {w} a = 1 := by
  have hne : (canonical G U W {w}).Nonempty := by
    by_contra hn
    have hz := not_nonempty_iff_eq_empty.mp hn
    have hh := mixed_canonical (G := G) U W {w}
    rw [hz] at hh
    simp [mixedTheta] at hh
    omega
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hxU, hxrow⟩ := mem_filter.mp hx
  have hx1 : dg G {w} x ≤ 1 := by simpa using dg_le_card (G := G) {w} x
  have hx4 := h.minU x hxU
  have hxdeg : dg G W x = 4 := by unfold row at hxrow; omega
  have hxa := only_four h ha hd hxU hxdeg
  subst x
  unfold row at hxrow
  omega

lemma positive_four_bound {U W T : Finset V} (h : QB6Assembly.C3SInput G U W) {a : V}
    (ha : a ∈ U) (hd : dg G W a = 4) (hT : T ⊆ W) (hne : T.Nonempty)
    (hp : 1 ≤ capTheta G U W T) : df G U T ≤ 2 * (dg G T a : ℤ) := by
  have htpos := card_pos.mpr hne
  have htfull : T ≠ W := fun he => by rw [he, theta_full h] at hp; omega
  have hlt : #T < #W := card_lt_card ⟨hT, fun he => htfull (Subset.antisymm hT he)⟩
  rcases (by omega : #T = 1 ∨ #T = 2 ∨ 3 ≤ #T) with h1 | h2 | h3
  · obtain ⟨w, rfl⟩ := card_eq_one.mp h1
    have hwa := positive_singleton_four h ha hd hp
    have hw := h.minW w (hT (mem_singleton_self w))
    simp only [df, sum_singleton, hwa]
    omega
  · have hc := theta_two_le h h2
    omega
  · let X := canonical G U W T
    have hX : X ⊆ U := canonical_subset (G := G) U W T
    have hs := positive_signature h hT hlt h3 hp
    change PositiveSignature ((#X : ℤ)-#T) (gv G X T) (df G W X) _ at hs
    have hdX : 2 ≤ df G W X := by rcases hs with hh|hh|hh|hh|hh <;> omega
    have haX := four_mem_of_def h ha hd hX hdX
    have hi := canonical_internal h hT hlt h3 haX
    change 20 ≤ gv G X T + 2 * (dg G T a : ℤ) at hi
    have hdf := df_anti (G := G) (Z := T) hX
    have hgv := gv_eq_left (G := G) X T
    rcases hs with hh|hh|hh|hh|hh <;> omega

omit [DecidableEq V] in
lemma theta_singleton_zero_of_five {U W : Finset V} (hmin : ∀ a ∈ U, 5 ≤ dg G W a) (w : V) :
    capTheta G U W {w} = 0 := by
  have hs : (∑ a ∈ U, max 0 (row G W {w} a)) = 0 := by
    apply sum_eq_zero
    intro a ha
    have hm := hmin a ha
    have hd : dg G {w} a ≤ 1 := by simpa using dg_le_card (G := G) {w} a
    apply max_eq_left
    unfold row
    omega
  simp [capTheta, hs]

omit [DecidableEq V] in
lemma weighted_full_five {U W : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hmin : ∀ a ∈ U, 5 ≤ dg G W a) : weightedDegree G U W W = 15 := by
  have hp : ∀ a ∈ U, (6-(dg G W a : ℤ)) * (dg G W a : ℤ) =
      5 * (6-(dg G W a : ℤ)) := by
    intro a ha
    have hm := hmin a ha
    have hc := h.capU a ha
    rcases (by omega : dg G W a = 5 ∨ dg G W a = 6) with he|he <;> rw [he] <;> norm_num
  unfold weightedDegree
  rw [sum_congr rfl hp, ← mul_sum]
  change 5 * df G W U = 15
  rw [h.deficiency]
  norm_num

end C3SInput

/-! The following scaled induction credits QB5.C2P.budget's fixed 3/2 proof. -/
theorem budget_scaled {P B : Finset V} (f : V → Finset V) (d omegaW : V → ℤ)
    (alpha beta : ℤ) (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (hd : ∀ z ∈ B, 0 ≤ d z) (ho : ∀ z ∈ B, 0 ≤ omegaW z)
    (h1 : ∀ y ∈ P, y ∈ f y)
    (h2 : ∀ y ∈ P, ∀ y' ∈ P, f y = f y' ∨ Disjoint (f y) (f y'))
    (h3 : ∀ y ∈ P, f y ⊆ B)
    (h4 : ∀ y ∈ P, alpha * (∑ z ∈ f y, d z) ≤ beta * (∑ z ∈ f y, omegaW z)) :
    alpha * (∑ z ∈ P, d z) ≤ beta * (∑ z ∈ B, omegaW z) := by
  induction P using Finset.strongInduction generalizing B with
  | H P ih =>
    rcases P.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · simp only [sum_empty, mul_zero]
      exact mul_nonneg hb (sum_nonneg ho)
    · have hSB : f y ⊆ B := h3 y hy
      have hP' : P.filter (· ∉ f y) ⊂ P :=
        filter_ssubset.mpr ⟨y, hy, not_not.mpr (h1 y hy)⟩
      have hsub : ∀ z ∈ P.filter (· ∉ f y), f z ⊆ B \ f y := by
        intro z hz
        obtain ⟨hzP, hzS⟩ := mem_filter.mp hz
        rcases h2 z hzP y hy with heq | hdis
        · exact absurd (heq ▸ h1 z hzP) hzS
        · exact subset_sdiff.mpr ⟨h3 z hzP, hdis⟩
      have ih' := ih (P.filter (· ∉ f y)) hP' (B := B \ f y)
        (fun z hz => hd z (sdiff_subset hz)) (fun z hz => ho z (sdiff_subset hz))
        (fun z hz => h1 z (mem_filter.mp hz).1)
        (fun z hz z' hz' => h2 z (mem_filter.mp hz).1 z' (mem_filter.mp hz').1)
        hsub (fun z hz => h4 z (mem_filter.mp hz).1)
      have hsplitP := sum_filter_add_sum_filter_not P (· ∈ f y) d
      have hsplitB := sum_sdiff hSB (f := omegaW)
      have hin : (∑ z ∈ P.filter (· ∈ f y), d z) ≤ ∑ z ∈ f y, d z :=
        sum_le_sum_of_subset_of_nonneg (fun z hz => (mem_filter.mp hz).2)
          fun z hz _ => hd z (hSB hz)
      have hinScaled := mul_le_mul_of_nonneg_left hin ha
      have hy4 := h4 y hy
      nlinarith

omit [DecidableEq V] in
lemma singleton_degree_sum (M : Finset V) (a : V) :
    (∑ w ∈ M, (dg G {a} w : ℤ)) = (dg G M a : ℤ) := by
  rw [← Nat.cast_sum]
  change (ec G M {a} : ℤ) = (dg G M a : ℤ)
  rw [ec_comm]
  simp [ec]

def incidenceWeight (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) (w : V) : ℤ :=
  ∑ a ∈ U, (6-(dg G W a : ℤ)) * (dg G {a} w : ℤ)

omit [DecidableEq V] in
lemma incidence_sum (U W T : Finset V) :
    (∑ w ∈ T, incidenceWeight G U W w) = weightedDegree G U W T := by
  unfold incidenceWeight weightedDegree
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [← mul_sum, singleton_degree_sum]

omit [DecidableEq V] in
lemma incidence_nonneg {U W : Finset V} (h : QB6Assembly.C3SInput G U W) (w : V) :
    0 ≤ incidenceWeight G U W w := by
  apply sum_nonneg
  intro a ha
  have hc := h.capU a ha
  exact mul_nonneg (by omega) (Nat.cast_nonneg _)

theorem maximal_cover_of_not_quartic {U W : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hq : ¬ Quartic G U W) :
    ∃ F : V → Finset V, ∀ w ∈ W, w ∈ F w ∧
      FiniteTests.IsMaxPositive (capTheta G U W) W (F w) := by
  classical
  have hex : ∀ w : V, ∃ M : Finset V, w ∈ W →
      w ∈ M ∧ FiniteTests.IsMaxPositive (capTheta G U W) W M := by
    intro w
    by_cases hw : w ∈ W
    · have hp : ∃ T, T ⊆ W ∧ w ∈ T ∧ 1 ≤ capTheta G U W T := by
        by_contra hn
        have hgood : ∀ T ⊆ W, w ∈ T → capTheta G U W T ≤ 0 := by
          intro T hT hwT
          have hh : ¬ 1 ≤ capTheta G U W T := fun hp => hn ⟨T, hT, hwT, hp⟩
          omega
        exact hq (quartic_of_uncovered h.card (C3SInput.nonempty_U h) hw hgood)
      obtain ⟨T, hT, hwT, hp⟩ := hp
      obtain ⟨M, hTM, hM⟩ := FiniteTests.exists_max_positive hT ⟨w, hwT⟩ hp
      exact ⟨M, fun _ => ⟨hTM hwT, hM⟩⟩
    · exact ⟨∅, fun hh => (hw hh).elim⟩
  choose F hF using hex
  exact ⟨F, hF⟩

theorem quartic_of_no_hub {U W : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hno : ∀ T ⊆ W, T.Nonempty → capTheta G U W T ≤ 1) : Quartic G U W := by
  by_contra hq
  obtain ⟨F, hF⟩ := maximal_cover_of_not_quartic h hq
  have heqdis : ∀ w ∈ W, ∀ w' ∈ W, F w = F w' ∨ Disjoint (F w) (F w') := by
    intro w hw w' hw'
    by_cases he : F w = F w'
    · exact Or.inl he
    · exact Or.inr (FiniteTests.disjoint_of_no_two (cap_supermod (G := G) U W)
        hno (hF w hw).2 (hF w' hw').2 he)
  have hd : ∀ w ∈ W, (0 : ℤ) ≤ 6-(dg G U w : ℤ) :=
    fun w hw => by have hc := h.capW w hw; omega
  by_cases hfour : ∃ a ∈ U, dg G W a = 4
  · obtain ⟨a, ha, ha4⟩ := hfour
    have hb := budget_scaled F (fun w => 6-(dg G U w : ℤ))
      (fun w => (dg G {a} w : ℤ)) 1 2 (by norm_num) (by norm_num) hd
      (fun _ _ => Nat.cast_nonneg _) (fun w hw => (hF w hw).1) heqdis
      (fun w hw => (hF w hw).2.1) (fun w hw => by
        have hm := (hF w hw).2
        have hp := C3SInput.positive_four_bound h ha ha4 hm.1 hm.2.1 hm.2.2.1
        simpa only [df, one_mul, singleton_degree_sum] using hp)
    change 1 * df G U W ≤ 2 * (∑ w ∈ W, (dg G {a} w : ℤ)) at hb
    rw [singleton_degree_sum, ha4, C3SInput.defW h] at hb
    omega
  · have hmin : ∀ a ∈ U, 5 ≤ dg G W a := by
      intro a ha
      have hm := h.minU a ha
      have hn : dg G W a ≠ 4 := fun he => hfour ⟨a, ha, he⟩
      omega
    have hb := budget_scaled F (fun w => 6-(dg G U w : ℤ))
      (incidenceWeight G U W) 9 4 (by norm_num) (by norm_num) hd
      (fun w _ => incidence_nonneg h w) (fun w hw => (hF w hw).1) heqdis
      (fun w hw => (hF w hw).2.1) (fun w hw => by
        have hm := (hF w hw).2
        have hpos := card_pos.mpr hm.2.1
        have h3 : 3 ≤ #(F w) := by
          by_contra hn
          rcases (by omega : #(F w) = 1 ∨ #(F w) = 2) with h1 | h2
          · obtain ⟨y, hy⟩ := card_eq_one.mp h1
            have hz := C3SInput.theta_singleton_zero_of_five (G := G) hmin y
            have hp := hm.2.2.1
            rw [hy, hz] at hp
            omega
          · have hz := C3SInput.theta_two_le h h2
            have hp := hm.2.2.1
            omega
        have hneW : F w ≠ W := fun he => by
          have hp := hm.2.2.1
          rw [he, C3SInput.theta_full h] at hp
          omega
        have hlt : #(F w) < #W := card_lt_card ⟨hm.1, fun hh => hneW (Subset.antisymm hm.1 hh)⟩
        have hp := C3SInput.positive_weighted_bound h hm.1 hlt h3 hm.2.2.1
        simpa only [df, incidence_sum] using hp)
    change 9 * df G U W ≤ 4 * (∑ w ∈ W, incidenceWeight G U W w) at hb
    rw [incidence_sum, C3SInput.weighted_full_five h hmin, C3SInput.defW h] at hb
    omega

namespace C3SInput

lemma hub_shape {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) :
    capTheta G U W K = 2 ∧ 3 ≤ #K ∧ #K < #W ∧
      (#(canonical G U W K) : ℤ)-#K = 2 ∧
      gv G (canonical G U W K) K = 14 ∧ df G W (canonical G U W K) = 3 := by
  have hb := theta_nonempty_le h hK.1 hK.2.1
  have hp := hK.2.2.1
  have he : capTheta G U W K = 2 := by omega
  have hne : K ≠ W := fun hh => by rw [hh, theta_full h] at hp; omega
  have hlt : #K < #W := card_lt_card ⟨hK.1, fun hh => hne (Subset.antisymm hK.1 hh)⟩
  have hpos := card_pos.mpr hK.2.1
  have h3 : 3 ≤ #K := by
    by_contra hn
    rcases (by omega : #K = 1 ∨ #K = 2) with h1 | h2
    · obtain ⟨w, hw⟩ := card_eq_one.mp h1
      have hs := theta_singleton_le h w
      rw [hw] at hp
      omega
    · have hs := theta_two_le h h2
      omega
  have hs := positive_signature h hK.1 hlt h3 (by omega)
  refine ⟨he, h3, hlt, ?_⟩
  rcases hs with hh|hh|hh|hh|hh <;> omega

lemma hub_boundaries {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) :
    0 ≤ df G U K ∧ df G U K ≤ 1 ∧
      ec G (canonical G U W K) (W \ K) = 10 ∧
      (ec G K (U \ canonical G U W K) : ℤ) = 1-df G U K := by
  obtain ⟨_, _, _, hk, hg, hd⟩ := hub_shape h hK
  have hX := canonical_subset (G := G) U W K
  have hl := gv_eq_left (G := G) (canonical G U W K) K
  have hr := gv_eq_right (G := G) (canonical G U W K) K
  have hdK := df_nonneg (G := G) fun w hw => h.capW w (hK.1 hw)
  have h1 := df_eq_df_add_ec (G := G) hX K
  have h2 := df_eq_df_add_ec (G := G) hK.1 (canonical G U W K)
  exact ⟨hdK, by omega, by omega, by omega⟩

lemma hub_outside_six {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) {a : V}
    (ha : a ∈ U \ canonical G U W K) : dg G W a = 6 := by
  have hX := canonical_subset (G := G) U W K
  have hsplit := df_sdiff_add (G := G) (S := W) hX
  have hs := (hub_shape h hK).2.2.2.2.2
  have hd := h.deficiency
  apply dg_eq_six_of_df_eq_zero
    (fun x hx => h.capU x (sdiff_subset hx)) (by omega) ha

lemma hub_outside_reverse {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) {a : V}
    (ha : a ∈ U \ canonical G U W K) :
    (dg G K a : ℤ) ≤ 1-df G U K := by
  have he := single_le_sum (f := dg G K) (fun _ _ => Nat.zero_le _) ha
  change dg G K a ≤ ec G (U \ canonical G U W K) K at he
  rw [ec_comm] at he
  have hb := (hub_boundaries h hK).2.2.2
  omega

lemma hub_internal_three {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) {a : V}
    (ha : a ∈ canonical G U W K) : 3 ≤ dg G K a := by
  obtain ⟨_, h3, hlt, _, hg, _⟩ := hub_shape h hK
  have hi := canonical_internal h hK.1 hlt h3 ha
  omega

lemma hub_outside_forward {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) {w : V}
    (hw : w ∈ W \ K) : dg G (canonical G U W K) w ≤ 3 := by
  obtain ⟨_, h3, _, hk, hg, _⟩ := hub_shape h hK
  have hX := canonical_subset (G := G) U W K
  have hcx := card_le_card hX
  have hc := h.card
  have hi := card_insert_of_notMem (mem_sdiff.mp hw).2
  have hsp := h.sparse (canonical G U W K) hX (insert w K)
    (insert_subset (mem_sdiff.mp hw).1 hK.1) (by omega) (by omega)
  have he := gv_insert_right (G := G) (canonical G U W K) (mem_sdiff.mp hw).2
  omega

end C3SInput

def capBonus (G : SimpleGraph V) [DecidableRel G.Adj]
    (W M N : Finset V) (a : V) : ℤ :=
  max 0 (row G W (M ∪ N) a) + max 0 (row G W (M ∩ N) a) -
    max 0 (row G W M a) - max 0 (row G W N a)

lemma capBonus_nonneg (W M N : Finset V) (a : V) : 0 ≤ capBonus G W M N a := by
  have hsum := dg_union_add_dg_inter (G := G) M N a
  have h1 := dg_mono (G := G) (inter_subset_left : M ∩ N ⊆ M) a
  have h2 := dg_mono (G := G) (inter_subset_right : M ∩ N ⊆ N) a
  zify at hsum h1 h2
  have hh := pospart_supermod (dg G M a) (dg G N a) (dg G (M ∩ N) a)
    (dg G (M ∪ N) a) ((dg G W a : ℤ)-4) (by omega) h1 h2
  simpa [capBonus, row, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    (sub_nonneg.mpr hh)

lemma capBonus_sum (U W M N : Finset V) :
    (∑ a ∈ U, capBonus G W M N a) =
      capTheta G U W (M ∪ N) + capTheta G U W (M ∩ N) -
        capTheta G U W M - capTheta G U W N := by
  have hc := card_union_add_card_inter M N
  zify at hc
  simp only [capBonus, sum_sub_distrib, sum_add_distrib, capTheta]
  linarith

lemma capBonus_zero {U W M N : Finset V}
    (he : capTheta G U W (M ∪ N) + capTheta G U W (M ∩ N) =
      capTheta G U W M + capTheta G U W N) {a : V} (ha : a ∈ U) :
    capBonus G W M N a = 0 := by
  have hs := capBonus_sum (G := G) U W M N
  have hz : (∑ a ∈ U, capBonus G W M N a) = 0 := by omega
  exact (sum_eq_zero_iff_of_nonneg (fun x _ => capBonus_nonneg (G := G) W M N x)).mp hz a ha

theorem canonical_hub_intersection {U W K M N : Finset V}
    (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K)
    (hM : FiniteTests.IsMaxPositive (capTheta G U W) W M)
    (hN : FiniteTests.IsMaxPositive (capTheta G U W) W N)
    (hKM : K ⊆ M) (hKN : K ⊆ N) (hne : M ≠ N) :
    canonical G U W M ∩ canonical G U W N = canonical G U W K := by
  obtain ⟨hi, hm, hn, hu⟩ := FiniteTests.hub_intersection (cap_supermod (G := G) U W)
    (fun T hT hne => C3SInput.theta_nonempty_le h hT hne) hM hN hK hKM hKN hne
  have hk := (C3SInput.hub_shape h hK).1
  have he : capTheta G U W (M ∪ N) + capTheta G U W (M ∩ N) =
      capTheta G U W M + capTheta G U W N := by rw [hi, hm, hn, hu, hk]; norm_num
  apply Subset.antisymm
  · intro a ha
    obtain ⟨haM, haN⟩ := mem_inter.mp ha
    by_contra haK
    have haU : a ∈ U := canonical_subset (G := G) U W M haM
    have haOut : a ∈ U \ canonical G U W K := mem_sdiff.mpr ⟨haU, haK⟩
    have ha6 := C3SInput.hub_outside_six h hK haOut
    have hc := C3SInput.hub_outside_reverse h hK haOut
    have hd0 := (C3SInput.hub_boundaries h hK).1
    have hz := capBonus_zero he haU
    have hdm := (mem_filter.mp haM).2
    have hdn := (mem_filter.mp haN).2
    have hs := dg_union_add_dg_inter (G := G) M N a
    unfold capBonus at hz
    rw [hi] at hs hz
    simp only [row, ha6] at hz
    simp only [row, ha6] at hdm hdn
    omega
  · exact subset_inter (canonical_mono hKM) (canonical_mono hKN)

def petalU (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W K M : Finset V) : Finset V := canonical G U W M \ canonical G U W K

def petalW (K M : Finset V) : Finset V := M \ K

def petalCost (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W K M : Finset V) : ℕ :=
  ec G (canonical G U W K) (petalW K M) + ec G K (petalU G U W K M)

lemma gv_partition {H X K M : Finset V} (hH : H ⊆ X) (hK : K ⊆ M) :
    gv G (X \ H) (M \ K) = gv G X M - gv G H K +
      2 * ((ec G H (M \ K) : ℤ) + ec G K (X \ H)) := by
  have he1 := ec_sdiff_add_left (G := G) hH M
  have he2 := ec_sdiff_add_right (G := G) hK H
  have he3 := ec_sdiff_add_right (G := G) hK (X \ H)
  have he4 := ec_comm (G := G) (X \ H) K
  have hc1 := card_sdiff_add_card_eq_card hH
  have hc2 := card_sdiff_add_card_eq_card hK
  unfold gv
  omega

lemma petalU_subset {U W K M : Finset V} :
    petalU G U W K M ⊆ U \ canonical G U W K := by
  intro a ha
  obtain ⟨haM, haK⟩ := mem_sdiff.mp ha
  exact mem_sdiff.mpr ⟨canonical_subset (G := G) U W M haM, haK⟩

lemma petalW_subset {W K M : Finset V} (hM : M ⊆ W) : petalW K M ⊆ W \ K := by
  intro w hw
  exact mem_sdiff.mpr ⟨hM (mem_sdiff.mp hw).1, (mem_sdiff.mp hw).2⟩

namespace C3SInput

lemma strict_hub_maximum {U W K M : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K)
    (hM : FiniteTests.IsMaxPositive (capTheta G U W) W M)
    (hKM : K ⊆ M) (hne : M ≠ K) :
    capTheta G U W M = 1 ∧ df G W (canonical G U W M) = 3 ∧
      ((#(canonical G U W M) : ℤ)-#M = 1 ∧ gv G (canonical G U W M) M = 14 ∨
       (#(canonical G U W M) : ℤ)-#M = 2 ∧ gv G (canonical G U W M) M = 16 ∨
       (#(canonical G U W M) : ℤ)-#M = 3 ∧ gv G (canonical G U W M) M = 18) := by
  have hp := hM.2.2.1
  have hn2 : ¬ 2 ≤ capTheta G U W M := fun hh => hne (hK.2.2.2 M hM.1 hKM hh)
  have he : capTheta G U W M = 1 := by omega
  have hmf : M ≠ W := fun hh => by rw [hh, theta_full h] at hp; omega
  have hlt : #M < #W := card_lt_card ⟨hM.1, fun hh => hmf (Subset.antisymm hM.1 hh)⟩
  have h3 : 3 ≤ #M := (hub_shape h hK).2.1.trans (card_le_card hKM)
  have hX := canonical_subset (G := G) U W M
  have hdle := df_le_of_subset (G := G) hX h.capU
  have hdm := df_le_of_subset (G := G) (canonical_mono (G := G) (U := U) (W := W) hKM)
    (fun a ha => h.capU a (hX ha))
  have hdk := (hub_shape h hK).2.2.2.2.2
  have hdu := h.deficiency
  have hd : df G W (canonical G U W M) = 3 := by omega
  have hs := positive_signature h hM.1 hlt h3 hp
  refine ⟨he, hd, ?_⟩
  rcases hs with hh|hh|hh|hh|hh <;> omega

lemma petal_identities {U W K M : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K)
    (_hM : FiniteTests.IsMaxPositive (capTheta G U W) W M) (hKM : K ⊆ M) :
    ((#(petalU G U W K M) : ℤ)-#(petalW K M)) =
      (#(canonical G U W M) : ℤ)-#M-2 ∧
    gv G (petalU G U W K M) (petalW K M) =
      gv G (canonical G U W M) M-14+2*(petalCost G U W K M : ℤ) ∧
    df G U (petalW K M) = df G U M-df G U K := by
  have hH := canonical_mono (G := G) (U := U) (W := W) hKM
  have hc1 := card_sdiff_add_card_eq_card hH
  have hc2 := card_sdiff_add_card_eq_card hKM
  have hk := (hub_shape h hK).2.2.2.1
  have hg := (hub_shape h hK).2.2.2.2.1
  have hp := gv_partition (G := G) hH hKM
  have hd := df_sdiff_add (G := G) (S := U) hKM
  dsimp only [petalU, petalW, petalCost]
  exact ⟨by omega, by omega, by omega⟩

lemma petal_sparse {U W K M : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K)
    (hM : FiniteTests.IsMaxPositive (capTheta G U W) W M) (hKM : K ⊆ M)
    (h3 : 3 ≤ #(petalU G U W K M)+#(petalW K M)) :
    14 ≤ gv G (petalU G U W K M) (petalW K M) := by
  have hH := canonical_subset (G := G) U W K
  have hX := canonical_subset (G := G) U W M
  have hcX := card_le_card hX
  have hcM := card_le_card hM.1
  have hcU := card_sdiff_add_card_eq_card (canonical_mono (G := G) (U := U) (W := W) hKM)
  have hcW := card_sdiff_add_card_eq_card hKM
  have hk3 := (hub_shape h hK).2.1
  exact h.sparse _ (petalU_subset.trans sdiff_subset) _
    ((petalW_subset (K := K) hM.1).trans sdiff_subset) h3 (by dsimp only [petalU, petalW]; omega)

end C3SInput

def PetalSignature (x y e : ℕ) (d D k g : ℤ) : Prop :=
  (k = -1 ∧ g = 14 ∧
    ((x = 0 ∧ y = 1 ∧ e = 3 ∧ D ≤ 2) ∨ (3 ≤ x+y ∧ 7 ≤ e ∧ D ≤ 4-d))) ∨
  (k = 0 ∧ g = 16 ∧
    ((x = 1 ∧ y = 1 ∧ d = 0 ∧ e = 4 ∧ D ≤ 2) ∨ (4 ≤ x+y ∧ 6 ≤ e ∧ D ≤ 2-d))) ∨
  (k = 1 ∧ g = 18 ∧ D = 0 ∧ d = 0 ∧ 5 ≤ e)

theorem petal_signature {U W K M : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K)
    (hM : FiniteTests.IsMaxPositive (capTheta G U W) W M)
    (hKM : K ⊆ M) (hne : M ≠ K) :
    PetalSignature #(petalU G U W K M) #(petalW K M) (petalCost G U W K M)
      (df G U K) (df G U (petalW K M))
      ((#(petalU G U W K M) : ℤ)-#(petalW K M)) (gv G (canonical G U W M) M) := by
  obtain ⟨_, _, hs⟩ := C3SInput.strict_hub_maximum h hK hM hKM hne
  obtain ⟨hk, hg, hd⟩ := C3SInput.petal_identities h hK hM hKM
  have hd0 := (C3SInput.hub_boundaries h hK).1
  have hd1 := (C3SInput.hub_boundaries h hK).2.1
  have hD0 := df_nonneg (G := G) fun w hw => h.capW w ((petalW_subset (K := K) hM.1).trans sdiff_subset hw)
  have hdf := df_anti (G := G) (Z := M) (canonical_subset (G := G) U W M)
  have hgm := gv_eq_left (G := G) (canonical G U W M) M
  have hy : 1 ≤ #(petalW K M) := by
    apply card_pos.mpr
    exact sdiff_nonempty.mpr (fun hh => hne (Subset.antisymm hh hKM))
  rcases hs with hA|hB|hZ
  · obtain ⟨hkM, hgM⟩ := hA
    have hdA : df G U (petalW K M) ≤ 4-df G U K := by omega
    refine Or.inl ⟨by omega, hgM, ?_⟩
    by_cases hsmall : #(petalU G U W K M)+#(petalW K M) ≤ 2
    · have hx : petalU G U W K M = ∅ := card_eq_zero.mp (by omega)
      have hy1 : #(petalW K M) = 1 := by omega
      obtain ⟨w, hw⟩ := card_eq_one.mp hy1
      have hepart : gv G (petalU G U W K M) (petalW K M) = 6 := by simp [hx, hw, gv, ec]
      have hmin := h.minW w ((petalW_subset (K := K) hM.1).trans sdiff_subset (hw.symm ▸ mem_singleton_self w))
      have hdpart : df G U (petalW K M) ≤ 2 := by simp only [hw, df, sum_singleton]; omega
      exact Or.inl ⟨by omega, hy1, by omega, hdpart⟩
    · have h3 : 3 ≤ #(petalU G U W K M)+#(petalW K M) := by omega
      have hsp := C3SInput.petal_sparse h hK hM hKM h3
      exact Or.inr ⟨h3, by omega, hdA⟩
  · obtain ⟨hkM, hgM⟩ := hB
    have hdB : df G U (petalW K M) ≤ 2-df G U K := by omega
    refine Or.inr (Or.inl ⟨by omega, hgM, ?_⟩)
    by_cases hsmall : #(petalU G U W K M)+#(petalW K M) ≤ 3
    · have hx1 : #(petalU G U W K M) = 1 := by omega
      have hy1 : #(petalW K M) = 1 := by omega
      obtain ⟨a, ha⟩ := card_eq_one.mp hx1
      obtain ⟨w, hw⟩ := card_eq_one.mp hy1
      have hepart : 10 ≤ gv G (petalU G U W K M) (petalW K M) := by
        have hle : dg G {w} a ≤ 1 := by simpa using dg_le_card (G := G) {w} a
        simp only [ha, hw, gv, ec, sum_singleton, card_singleton]
        omega
      have haOut := petalU_subset (G := G) (U := U) (W := W) (K := K) (M := M)
        (ha.symm ▸ mem_singleton_self a)
      have hwOut := petalW_subset (K := K) hM.1 (hw.symm ▸ mem_singleton_self w)
      have haf := C3SInput.hub_outside_reverse h hK haOut
      have hwf := C3SInput.hub_outside_forward h hK hwOut
      have he : petalCost G U W K M = dg G (canonical G U W K) w + dg G K a := by
        simp only [petalCost, ha, hw]
        rw [ec_comm (G := G) (canonical G U W K) {w}, ec_comm (G := G) K {a}]
        simp [ec]
      exact Or.inl ⟨hx1, hy1, by omega, by omega, by omega⟩
    · have h4 : 4 ≤ #(petalU G U W K M)+#(petalW K M) := by omega
      have hsp := C3SInput.petal_sparse h hK hM hKM (by omega)
      exact Or.inr ⟨h4, by omega, hdB⟩
  · obtain ⟨hkM, hgM⟩ := hZ
    have h3 : 3 ≤ #(petalU G U W K M)+#(petalW K M) := by omega
    have hsp := C3SInput.petal_sparse h hK hM hKM h3
    exact Or.inr (Or.inr ⟨by omega, hgM, by omega, by omega, by omega⟩)

theorem ec_sum_disjoint_parts {ι : Type*} (S : Finset ι) (P : ι → Finset V)
    (A B : Finset V) (hdis : Set.PairwiseDisjoint (↑S) P)
    (hsub : ∀ i ∈ S, P i ⊆ B) :
    (∑ i ∈ S, ec G A (P i)) ≤ ec G A B := by
  classical
  have hbi : S.biUnion P ⊆ B := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := mem_biUnion.mp hx
    exact hsub i hi hx
  have hs : (∑ i ∈ S, ec G A (P i)) = ec G (S.biUnion P) A := by
    simp_rw [ec_comm (G := G) A]
    change (∑ i ∈ S, ∑ x ∈ P i, dg G A x) = ∑ x ∈ S.biUnion P, dg G A x
    exact (sum_biUnion hdis).symm
  rw [hs, ec_comm (G := G) A B]
  exact ec_mono_left hbi A

theorem hub_family_cost {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) (S : Finset (Finset V))
    (hS : ∀ M ∈ S, FiniteTests.IsMaxPositive (capTheta G U W) W M ∧ K ⊆ M ∧ M ≠ K) :
    (∑ M ∈ S, (petalCost G U W K M : ℤ)) ≤ 11-df G U K := by
  have hdisW : Set.PairwiseDisjoint (↑S) (petalW K) := by
    intro M hM N hN hne
    have hi := (FiniteTests.hub_intersection (cap_supermod (G := G) U W)
      (fun T hT hne => C3SInput.theta_nonempty_le h hT hne)
      (hS M hM).1 (hS N hN).1 hK (hS M hM).2.1 (hS N hN).2.1 hne).1
    apply disjoint_left.mpr
    intro w hwM hwN
    obtain ⟨hwM, hwK⟩ := mem_sdiff.mp hwM
    obtain ⟨hwN, _⟩ := mem_sdiff.mp hwN
    exact hwK (hi ▸ mem_inter.mpr ⟨hwM, hwN⟩)
  have hdisU : Set.PairwiseDisjoint (↑S) (petalU G U W K) := by
    intro M hM N hN hne
    have hi := canonical_hub_intersection h hK (hS M hM).1 (hS N hN).1
      (hS M hM).2.1 (hS N hN).2.1 hne
    apply disjoint_left.mpr
    intro a haM haN
    obtain ⟨haM, haK⟩ := mem_sdiff.mp haM
    obtain ⟨haN, _⟩ := mem_sdiff.mp haN
    exact haK (hi ▸ mem_inter.mpr ⟨haM, haN⟩)
  have hw := ec_sum_disjoint_parts (G := G) S (petalW K)
    (canonical G U W K) (W \ K) hdisW (fun M hM => petalW_subset (hS M hM).1.1)
  have hu := ec_sum_disjoint_parts (G := G) S (petalU G U W K)
    K (U \ canonical G U W K) hdisU (fun _ _ => petalU_subset)
  have hb := C3SInput.hub_boundaries h hK
  have hsum : (∑ M ∈ S, (petalCost G U W K M : ℤ)) =
      (∑ M ∈ S, (ec G (canonical G U W K) (petalW K M) : ℤ)) +
      (∑ M ∈ S, (ec G K (petalU G U W K M) : ℤ)) := by
    simp [petalCost, sum_add_distrib]
  rw [hsum]
  zify at hw hu
  omega

theorem petal_floor_bound {U W K M : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K)
    (hM : FiniteTests.IsMaxPositive (capTheta G U W) W M) (hKM : K ⊆ M) (hne : M ≠ K) :
    df G U (petalW K M) ≤ 2 * ((petalCost G U W K M / 3 : ℕ) : ℤ) := by
  have hs := petal_signature h hK hM hKM hne
  have hd := (C3SInput.hub_boundaries h hK).1
  rcases hs with ⟨_, _, hA⟩|⟨_, _, hB⟩|hZ
  · rcases hA with hA|hA <;> omega
  · rcases hB with hB|hB <;> omega
  · omega

theorem hub_family_defect {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) (S : Finset (Finset V))
    (hS : ∀ M ∈ S, FiniteTests.IsMaxPositive (capTheta G U W) W M ∧ K ⊆ M ∧ M ≠ K) :
    (∑ M ∈ S, df G U (petalW K M)) ≤ 6 := by
  have hb := hub_family_cost h hK S hS
  have hd0 := (C3SInput.hub_boundaries h hK).1
  have hfloor : 3 * (∑ M ∈ S, ((petalCost G U W K M / 3 : ℕ) : ℤ)) ≤
      ∑ M ∈ S, (petalCost G U W K M : ℤ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro M _
    omega
  have hsum := sum_le_sum (fun M hM => petal_floor_bound h hK
    (hS M hM).1 (hS M hM).2.1 (hS M hM).2.2)
  rw [← mul_sum] at hsum
  have hf : (∑ M ∈ S, ((petalCost G U W K M / 3 : ℕ) : ℤ)) ≤ 3 := by omega
  omega

theorem hub_family_equality {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) (S : Finset (Finset V))
    (hS : ∀ M ∈ S, FiniteTests.IsMaxPositive (capTheta G U W) W M ∧ K ⊆ M ∧ M ≠ K)
    (hd : df G U K = 1) (he : (∑ M ∈ S, df G U (petalW K M)) = 6) :
    #S = 3 ∧ ∀ M ∈ S, #(petalU G U W K M) = 0 ∧ #(petalW K M) = 1 ∧
      petalCost G U W K M = 3 ∧ df G U (petalW K M) = 2 := by
  have hb := hub_family_cost h hK S hS
  have hf : 3 * (∑ M ∈ S, ((petalCost G U W K M / 3 : ℕ) : ℤ)) ≤
      ∑ M ∈ S, (petalCost G U W K M : ℤ) := by
    rw [mul_sum]
    exact sum_le_sum (fun M _ => by omega)
  have hl : ∀ M ∈ S, 0 ≤ 2 * ((petalCost G U W K M / 3 : ℕ) : ℤ)-df G U (petalW K M) :=
    fun M hM => by have := petal_floor_bound h hK (hS M hM).1 (hS M hM).2.1 (hS M hM).2.2; omega
  have hsum := sum_nonneg hl
  simp only [sum_sub_distrib, ← mul_sum] at hsum
  have hfloor : (∑ M ∈ S, ((petalCost G U W K M / 3 : ℕ) : ℤ)) = 3 := by omega
  have hz : (∑ M ∈ S, (2 * ((petalCost G U W K M / 3 : ℕ) : ℤ)-df G U (petalW K M))) = 0 := by
    rw [sum_sub_distrib, ← mul_sum, he, hfloor]; norm_num
  have hgap := (sum_eq_zero_iff_of_nonneg hl).mp hz
  have hparts : ∀ M ∈ S, #(petalU G U W K M) = 0 ∧ #(petalW K M) = 1 ∧
      petalCost G U W K M = 3 ∧ df G U (petalW K M) = 2 := by
    intro M hM
    have hh := hgap M hM
    have hs := petal_signature h hK (hS M hM).1 (hS M hM).2.1 (hS M hM).2.2
    rcases hs with ⟨_, _, hA⟩|⟨_, _, hB⟩|hZ
    · rcases hA with hA|hA <;> omega
    · rcases hB with hB|hB <;> omega
    · omega
  have ht : (∑ M ∈ S, ((petalCost G U W K M / 3 : ℕ) : ℤ)) = #S := by
    calc
      _ = ∑ M ∈ S, (1 : ℤ) := sum_congr rfl (fun M hM => by rw [(hparts M hM).2.2.1]; norm_num)
      _ = #S := by simp
  exact ⟨by omega, hparts⟩

namespace C3SInput

lemma deficient_mem_hub {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) {a : V}
    (ha : a ∈ U) (hd : dg G W a ≤ 5) : a ∈ canonical G U W K := by
  by_contra hn
  have hs := hub_outside_six h hK (mem_sdiff.mpr ⟨ha, hn⟩)
  omega

omit [DecidableEq V] in
lemma deficient_in_canonical {U W M : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hd : 1 ≤ df G W (canonical G U W M)) :
    ∃ a ∈ canonical G U W M, dg G W a ≤ 5 := by
  by_contra hn
  have hs : df G W (canonical G U W M) = 0 := by
    apply sum_eq_zero
    intro a ha
    have hc := h.capU a (canonical_subset (G := G) U W M ha)
    have hh : ¬ dg G W a ≤ 5 := fun hh => hn ⟨a, ha, hh⟩
    omega
  omega

lemma disjoint_hub_fourteen_impossible {U W K M : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K)
    (hM : M ⊆ W) (hlt : #M < #W) (h3 : 3 ≤ #M) (hdis : Disjoint K M)
    (hg : gv G (canonical G U W M) M = 14) (hd : 1 ≤ df G W (canonical G U W M)) : False := by
  obtain ⟨a, haM, ha5⟩ := deficient_in_canonical h hd
  have haU := canonical_subset (G := G) U W M haM
  have haK := deficient_mem_hub h hK haU ha5
  have hK3 := hub_internal_three h hK haK
  have hM3 := canonical_internal h hM hlt h3 haM
  have hs := dg_union_of_disjoint (G := G) hdis a
  have hm := dg_mono (G := G) (union_subset hK.1 hM) a
  omega

lemma disjoint_hub_sixteen_impossible {U W K M : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K)
    (hM : M ⊆ W) (hlt : #M < #W) (h3 : 3 ≤ #M) (hdis : Disjoint K M)
    (hk : (#(canonical G U W M) : ℤ)-#M = 2)
    (hg : gv G (canonical G U W M) M = 16) (hd : df G W (canonical G U W M) = 3) : False := by
  by_cases hfour : ∃ a ∈ U, dg G W a = 4
  · obtain ⟨a, ha, ha4⟩ := hfour
    have haM := four_mem_of_def h ha ha4 (canonical_subset (G := G) U W M) (by omega)
    have haK := deficient_mem_hub h hK ha (by omega)
    have hK3 := hub_internal_three h hK haK
    have hM2 := canonical_internal h hM hlt h3 haM
    have hs := dg_union_of_disjoint (G := G) hdis a
    have hm := dg_mono (G := G) (union_subset hK.1 hM) a
    omega
  · let H := canonical G U W K
    let X := canonical G U W M
    have hHU : H ⊆ U := canonical_subset (G := G) U W K
    have hXU : X ⊆ U := canonical_subset (G := G) U W M
    have hmin : ∀ a ∈ U, 5 ≤ dg G W a := by
      intro a ha
      have hm := h.minU a ha
      have hh : dg G W a ≠ 4 := fun hh => hfour ⟨a, ha, hh⟩
      omega
    have hz : df G W (X \ (X ∩ H)) = 0 := by
      apply sum_eq_zero
      intro a ha
      obtain ⟨haX, hnot⟩ := mem_sdiff.mp ha
      have haH : a ∉ H := fun hh => hnot (mem_inter.mpr ⟨haX, hh⟩)
      have ha6 := hub_outside_six h hK (mem_sdiff.mpr ⟨hXU haX, haH⟩)
      omega
    have hsplit := df_sdiff_add (G := G) (S := W) (inter_subset_left : X ∩ H ⊆ X)
    have hdi : df G W (X ∩ H) = 3 := by change df G W X = 3 at hd; omega
    have hci : 3 ≤ #(X ∩ H) := by
      have hh : df G W (X ∩ H) ≤ #(X ∩ H) := by
        calc
          _ ≤ ∑ a ∈ X ∩ H, (1 : ℤ) := sum_le_sum (fun a ha => by have := hmin a (hXU (mem_inter.mp ha).1); omega)
          _ = #(X ∩ H) := by simp
      omega
    have hzero : K ∩ M = ∅ := disjoint_iff_inter_eq_empty.mp hdis
    have hpot := gv_union_add_gv_inter_le (G := G) H X K M
    have hHgv : gv G H K = 14 := (hub_shape h hK).2.2.2.2.1
    have hHk : (#H : ℤ)-#K = 2 := (hub_shape h hK).2.2.2.1
    change gv G X M = 16 at hg
    change (#X : ℤ)-#M = 2 at hk
    rw [hzero] at hpot
    have hInt : gv G (H ∩ X) ∅ = 6*(#(X ∩ H) : ℤ) := by simp [gv, ec, dg, inter_comm]
    rw [hInt] at hpot
    have hUS : H ∪ X ⊆ U := union_subset hHU hXU
    have hWS : K ∪ M ⊆ W := union_subset hK.1 hM
    have hcU := card_le_card hUS
    have hcW := card_le_card hWS
    have hcardU := card_union_add_card_inter H X
    have hcardW := card_union_add_card_inter K M
    simp only [hzero, card_empty] at hcardW
    have hIntCard : #(H ∩ X) = #(X ∩ H) := by rw [inter_comm]
    by_cases hproper : #(H ∪ X)+#(K ∪ M) < #U+#W
    · have hsp := h.sparse _ hUS _ hWS (by have := (hub_shape h hK).2.1; have := card_le_card (subset_union_left : K ⊆ K ∪ M); omega) hproper
      omega
    · have hUE : H ∪ X = U := eq_of_subset_of_card_le hUS (by omega)
      have hWE : K ∪ M = W := eq_of_subset_of_card_le hWS (by omega)
      rw [hUE, hWE, gv_full h] at hpot
      have hcard := h.card
      omega

theorem disjoint_hub_big_signature {U W K M : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K)
    (hM : FiniteTests.IsMaxPositive (capTheta G U W) W M)
    (hdis : Disjoint K M) (h3 : 3 ≤ #M) :
    (#(canonical G U W M) : ℤ)-#M = 3 ∧ gv G (canonical G U W M) M = 18 ∧
      df G W (canonical G U W M) = 3 ∧ df G U M = 0 := by
  have hp := hM.2.2.1
  have hmf : M ≠ W := fun hh => by rw [hh, theta_full h] at hp; omega
  have hlt : #M < #W := card_lt_card ⟨hM.1, fun hh => hmf (Subset.antisymm hM.1 hh)⟩
  have hs := positive_signature h hM.1 hlt h3 hp
  rcases hs with hA|hB|hP|hH|hZ
  · exact (disjoint_hub_fourteen_impossible h hK hM.1 hlt h3 hdis hA.2.1 (by omega)).elim
  · exact (disjoint_hub_sixteen_impossible h hK hM.1 hlt h3 hdis hB.1 hB.2.1 hB.2.2.1).elim
  · exact (disjoint_hub_fourteen_impossible h hK hM.1 hlt h3 hdis hP.2.1 (by omega)).elim
  · exact (disjoint_hub_fourteen_impossible h hK hM.1 hlt h3 hdis hH.2.1 (by omega)).elim
  · have hdf := df_anti (G := G) (Z := M) (canonical_subset (G := G) U W M)
    have hgm := gv_eq_left (G := G) (canonical G U W M) M
    have hd0 := df_nonneg (G := G) (Z := M) fun w hw => h.capW w (hM.1 hw)
    exact ⟨hZ.1, hZ.2.1, hZ.2.2.1, by omega⟩

end C3SInput

noncomputable def positiveMaxima (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) : Finset (Finset V) := by
  classical
  exact W.powerset.filter fun M => FiniteTests.IsMaxPositive (capTheta G U W) W M

noncomputable def aboveHub (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W K : Finset V) : Finset (Finset V) := by
  classical
  exact (positiveMaxima G U W).filter fun M => K ⊆ M ∧ M ≠ K

noncomputable def petalsW (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W K : Finset V) : Finset V := (aboveHub G U W K).biUnion (petalW K)

noncomputable def residualW (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W K : Finset V) : Finset V := W \ (K ∪ petalsW G U W K)

def MaximalCover (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) : Prop :=
  ∀ w ∈ W, ∃ M ∈ positiveMaxima G U W, w ∈ M

omit [DecidableEq V] in
lemma positiveMaxima_mem {U W M : Finset V} :
    M ∈ positiveMaxima G U W ↔ FiniteTests.IsMaxPositive (capTheta G U W) W M := by
  classical
  constructor
  · exact fun hm => (mem_filter.mp hm).2
  · exact fun hm => mem_filter.mpr ⟨mem_powerset.mpr hm.1, hm⟩

lemma aboveHub_mem {U W K M : Finset V} :
    M ∈ aboveHub G U W K ↔
      FiniteTests.IsMaxPositive (capTheta G U W) W M ∧ K ⊆ M ∧ M ≠ K := by
  classical
  simp only [aboveHub, mem_filter, positiveMaxima_mem]

lemma petalsW_subset {U W K : Finset V} : petalsW G U W K ⊆ W \ K := by
  intro w hw
  obtain ⟨M, hM, hw⟩ := mem_biUnion.mp hw
  exact petalW_subset (aboveHub_mem.mp hM).1.1 hw

lemma petalsW_disjoint {U W K : Finset V} : Disjoint K (petalsW G U W K) := by
  apply disjoint_left.mpr
  intro w hwK hwP
  exact (mem_sdiff.mp (petalsW_subset hwP)).2 hwK

theorem aboveHub_pairwise {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) :
    Set.PairwiseDisjoint (↑(aboveHub G U W K)) (petalW K) := by
  intro M hM N hN hne
  obtain ⟨hM, hKM, _⟩ := aboveHub_mem.mp hM
  obtain ⟨hN, hKN, _⟩ := aboveHub_mem.mp hN
  have hi := (FiniteTests.hub_intersection (cap_supermod (G := G) U W)
    (fun T hT hne => C3SInput.theta_nonempty_le h hT hne) hM hN hK hKM hKN hne).1
  apply disjoint_left.mpr
  intro w hwM hwN
  obtain ⟨hwM, hwK⟩ := mem_sdiff.mp hwM
  obtain ⟨hwN, _⟩ := mem_sdiff.mp hwN
  exact hwK (hi ▸ mem_inter.mpr ⟨hwM, hwN⟩)

theorem df_cover_partition {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) :
    df G U W = df G U K +
      (∑ M ∈ aboveHub G U W K, df G U (petalW K M)) + df G U (residualW G U W K) := by
  have hB : K ∪ petalsW G U W K ⊆ W := union_subset hK.1 (petalsW_subset.trans sdiff_subset)
  have hs := df_sdiff_add (G := G) (S := U) hB
  have hp : df G U (petalsW G U W K) = ∑ M ∈ aboveHub G U W K, df G U (petalW K M) := by
    exact sum_biUnion (aboveHub_pairwise h hK)
  have hb : df G U (K ∪ petalsW G U W K) = df G U K + df G U (petalsW G U W K) :=
    sum_union petalsW_disjoint
  change df G U (residualW G U W K) + df G U (K ∪ petalsW G U W K) = df G U W at hs
  omega

theorem maximal_cover_of_not_quartic' {U W : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hq : ¬ Quartic G U W) : MaximalCover G U W := by
  obtain ⟨F, hF⟩ := maximal_cover_of_not_quartic h hq
  intro w hw
  exact ⟨F w, positiveMaxima_mem.mpr (hF w hw).2, (hF w hw).1⟩

theorem residual_maximum_disjoint {U W K M : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K)
    (hM : FiniteTests.IsMaxPositive (capTheta G U W) W M) {w : V}
    (hw : w ∈ residualW G U W K) (hwM : w ∈ M) : Disjoint K M := by
  classical
  obtain ⟨hwW, hwB⟩ := mem_sdiff.mp hw
  have hwK : w ∉ K := fun hh => hwB (mem_union.mpr (Or.inl hh))
  apply disjoint_left.mpr
  intro z hzK hzM
  have hi : (M ∩ K).Nonempty := ⟨z, mem_inter.mpr ⟨hzM, hzK⟩⟩
  have hKM := FiniteTests.hub_subset (cap_supermod (G := G) U W)
    (fun T hT hne => C3SInput.theta_nonempty_le h hT hne) hM hK hi
  have hne : M ≠ K := fun hh => hwK (hh ▸ hwM)
  have hMA : M ∈ aboveHub G U W K := aboveHub_mem.mpr ⟨hM, hKM, hne⟩
  have hwP : w ∈ petalsW G U W K := mem_biUnion.mpr ⟨M, hMA, mem_sdiff.mpr ⟨hwM, hwK⟩⟩
  exact hwB (mem_union.mpr (Or.inr hwP))

theorem residual_positive_singleton {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) (hcover : MaximalCover G U W)
    {w : V} (hw : w ∈ residualW G U W K) (hd : 1 ≤ 6-(dg G U w : ℤ)) :
    1 ≤ capTheta G U W {w} := by
  have hwW : w ∈ W := sdiff_subset hw
  obtain ⟨M, hM, hwM⟩ := hcover w hwW
  have hmax := positiveMaxima_mem.mp hM
  have hdis := residual_maximum_disjoint h hK hmax hw hwM
  have hcpos := card_pos.mpr hmax.2.1
  rcases (by omega : #M = 1 ∨ #M = 2 ∨ 3 ≤ #M) with h1|h2|h3
  · obtain ⟨y, hy⟩ := card_eq_one.mp h1
    have hwy : w = y := mem_singleton.mp (hy ▸ hwM)
    simpa [hy, hwy] using hmax.2.2.1
  · have hz := C3SInput.theta_two_le h h2
    have hp := hmax.2.2.1
    omega
  · have hbig := C3SInput.disjoint_hub_big_signature h hK hmax hdis h3
    have hport := single_le_sum (f := fun y => (6 : ℤ)-dg G U y)
      (fun y hy => by have hc := h.capW y (hmax.1 hy); omega) hwM
    change 6-(dg G U w : ℤ) ≤ df G U M at hport
    omega

theorem residual_zero_of_no_four {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) (hcover : MaximalCover G U W)
    (hno : ¬ ∃ a ∈ U, dg G W a = 4) : df G U (residualW G U W K) = 0 := by
  have hmin : ∀ a ∈ U, 5 ≤ dg G W a := by
    intro a ha
    have hm := h.minU a ha
    have hn : dg G W a ≠ 4 := fun hh => hno ⟨a, ha, hh⟩
    omega
  apply sum_eq_zero
  intro w hw
  have hm := h.capW w (sdiff_subset hw)
  by_contra hn
  have hp : 1 ≤ 6-(dg G U w : ℤ) := by omega
  have ht := residual_positive_singleton h hK hcover hw hp
  have hz := C3SInput.theta_singleton_zero_of_five (G := G) hmin w
  omega

theorem residual_four_bound {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) (hcover : MaximalCover G U W)
    {a : V} (ha : a ∈ U) (ha4 : dg G W a = 4) :
    df G U (residualW G U W K) ≤ 2*(dg G (residualW G U W K) a : ℤ) ∧
      dg G (residualW G U W K) a ≤ 1 := by
  have hpoint : ∀ w ∈ residualW G U W K,
      6-(dg G U w : ℤ) ≤ 2*(dg G {a} w : ℤ) := by
    intro w hw
    have hwW : w ∈ W := sdiff_subset hw
    have hm := h.minW w hwW
    by_cases hp : 1 ≤ 6-(dg G U w : ℤ)
    · have ht := residual_positive_singleton h hK hcover hw hp
      have hadj := C3SInput.positive_singleton_four h ha ha4 ht
      have hcom : dg G {a} w = dg G {w} a := by
        have hh := ec_comm (G := G) {a} {w}
        simpa [ec] using hh.symm
      omega
    · omega
  have hs := sum_le_sum hpoint
  rw [← mul_sum, singleton_degree_sum] at hs
  have haK := C3SInput.deficient_mem_hub h hK ha (by omega)
  have hK3 := C3SInput.hub_internal_three h hK haK
  have hd := dg_sdiff_add (G := G) hK.1 a
  have hsub : residualW G U W K ⊆ W \ K := by
    intro w hw
    obtain ⟨hwW, hwn⟩ := mem_sdiff.mp hw
    exact mem_sdiff.mpr ⟨hwW, fun hh => hwn (mem_union.mpr (Or.inl hh))⟩
  have hmono := dg_mono (G := G) hsub a
  exact ⟨hs, by omega⟩

theorem hub_equality_of_cover {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) (hcover : MaximalCover G U W) :
    df G U K = 1 ∧ (∑ M ∈ aboveHub G U W K, df G U (petalW K M)) = 6 ∧
      df G U (residualW G U W K) = 2 ∧ ∃ a ∈ U, dg G W a = 4 := by
  have hb := hub_family_defect h hK (aboveHub G U W K) (fun _ hm => aboveHub_mem.mp hm)
  have hd := C3SInput.hub_boundaries h hK
  have hs := df_cover_partition h hK
  have hw := C3SInput.defW h
  by_cases hfour : ∃ a ∈ U, dg G W a = 4
  · obtain ⟨a, ha, ha4⟩ := hfour
    have hr := residual_four_bound h hK hcover ha ha4
    exact ⟨by omega, by omega, by omega, a, ha, ha4⟩
  · have hr := residual_zero_of_no_four h hK hcover hfour
    omega

omit [DecidableEq V] in
theorem unique_neighbor {B : Finset V} {a y : V} (hy : y ∈ B) (hay : G.Adj a y)
    (hd : dg G B a ≤ 1) : ∀ w ∈ B, G.Adj a w → w = y := by
  have hp : 0 < dg G B a := card_pos.mpr ⟨y, mem_filter.mpr ⟨hy, hay⟩⟩
  have he : dg G B a = 1 := by omega
  obtain ⟨z, hz⟩ := card_eq_one.mp he
  have hyz : y = z := mem_singleton.mp (hz ▸ mem_filter.mpr ⟨hy, hay⟩)
  intro w hw haw
  have hwz : w = z := mem_singleton.mp (hz ▸ mem_filter.mpr ⟨hw, haw⟩)
  exact hwz.trans hyz.symm

omit [DecidableEq V] in
theorem singleton_adj_of_degree_one {a w : V} (h : dg G {w} a = 1) : G.Adj a w := by
  by_contra hn
  have hz : dg G {w} a = 0 := by simp [dg, hn]
  omega

theorem residual_eq_singleton {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) (hcover : MaximalCover G U W)
    {a : V} (ha : a ∈ U) (ha4 : dg G W a = 4)
    (hr : df G U (residualW G U W K) = 2) :
    ∃ y, residualW G U W K = {y} := by
  classical
  have hex : ∃ y ∈ residualW G U W K, 1 ≤ 6-(dg G U y : ℤ) := by
    by_contra hn
    have hb : df G U (residualW G U W K) ≤ 0 := sum_nonpos (fun y hy => by
      have hh : ¬ 1 ≤ 6-(dg G U y : ℤ) := fun hh => hn ⟨y, hy, hh⟩
      omega)
    omega
  obtain ⟨y, hyR, hyd⟩ := hex
  have hyW : y ∈ W := sdiff_subset hyR
  have hyK : y ∉ K := fun hh => (mem_sdiff.mp hyR).2 (mem_union.mpr (Or.inl hh))
  have hyPos := residual_positive_singleton h hK hcover hyR hyd
  have hay := singleton_adj_of_degree_one (C3SInput.positive_singleton_four h ha ha4 hyPos)
  have haK := C3SInput.deficient_mem_hub h hK ha (by omega)
  have hK3 := C3SInput.hub_internal_three h hK haK
  have hdeg := dg_sdiff_add (G := G) hK.1 a
  have hunique := unique_neighbor (mem_sdiff.mpr ⟨hyW, hyK⟩) hay (by omega : dg G (W \ K) a ≤ 1)
  refine ⟨y, Subset.antisymm ?_ (singleton_subset_iff.mpr hyR)⟩
  intro w hw
  have hwW : w ∈ W := sdiff_subset hw
  have hwK : w ∉ K := fun hh => (mem_sdiff.mp hw).2 (mem_union.mpr (Or.inl hh))
  obtain ⟨M, hM, hwM⟩ := hcover w hwW
  have hmax := positiveMaxima_mem.mp hM
  have hdis := residual_maximum_disjoint h hK hmax hw hwM
  have hcpos := card_pos.mpr hmax.2.1
  rcases (by omega : #M = 1 ∨ #M = 2 ∨ 3 ≤ #M) with h1|h2|h3
  · obtain ⟨z, hz⟩ := card_eq_one.mp h1
    have hwz : w = z := mem_singleton.mp (hz ▸ hwM)
    have hpw : 1 ≤ capTheta G U W {w} := by simpa [hz, hwz] using hmax.2.2.1
    have haw := singleton_adj_of_degree_one (C3SInput.positive_singleton_four h ha ha4 hpw)
    exact mem_singleton.mpr (hunique w (mem_sdiff.mpr ⟨hwW, hwK⟩) haw)
  · have hz := C3SInput.theta_two_le h h2
    have hp := hmax.2.2.1
    omega
  · have hbig := C3SInput.disjoint_hub_big_signature h hK hmax hdis h3
    have haM := C3SInput.four_mem_of_def h ha ha4 (canonical_subset (G := G) U W M) (by omega)
    have haRow := (mem_filter.mp haM).2
    have haD : 0 < dg G M a := by unfold row at haRow; omega
    obtain ⟨z, hz⟩ := card_pos.mp haD
    obtain ⟨hzM, haz⟩ := mem_filter.mp hz
    have hzK : z ∉ K := fun hh => disjoint_left.mp hdis hh hzM
    have hzy := hunique z (mem_sdiff.mpr ⟨hmax.1 hzM, hzK⟩) haz
    have hyM : y ∈ M := hzy ▸ hzM
    have hport := single_le_sum (f := fun z => (6 : ℤ)-dg G U z)
      (fun z hz => by have hc := h.capW z (hmax.1 hz); omega) hyM
    change 6-(dg G U y : ℤ) ≤ df G U M at hport
    omega

theorem not_hub_cover {U W K : Finset V} (h : QB6Assembly.C3SInput G U W)
    (hK : FiniteTests.IsMaxTwo (capTheta G U W) W K) (hcover : MaximalCover G U W) : False := by
  classical
  obtain ⟨hd, hsum, hr, a, ha, ha4⟩ := hub_equality_of_cover h hK hcover
  obtain ⟨y, hR⟩ := residual_eq_singleton h hK hcover ha ha4 hr
  obtain ⟨hcardS, hparts⟩ := hub_family_equality h hK (aboveHub G U W K)
    (fun _ hm => aboveHub_mem.mp hm) hd hsum
  have hcardP : #(petalsW G U W K) = 3 := by
    unfold petalsW
    rw [card_biUnion (aboveHub_pairwise h hK)]
    calc
      _ = ∑ M ∈ aboveHub G U W K, (1 : ℕ) := sum_congr rfl (fun M hM => (hparts M hM).2.1)
      _ = #(aboveHub G U W K) := by simp
      _ = 3 := hcardS
  have hB : K ∪ petalsW G U W K ⊆ W := union_subset hK.1 (petalsW_subset.trans sdiff_subset)
  have hcardB := card_union_of_disjoint (petalsW_disjoint (G := G) (U := U) (W := W) (K := K))
  have hcardR := card_sdiff_add_card_eq_card hB
  change #(residualW G U W K)+#(K ∪ petalsW G U W K) = #W at hcardR
  rw [hR, card_singleton, hcardB, hcardP] at hcardR
  have hcardW := card_sdiff_add_card_eq_card hK.1
  have hBW : #(W \ K) = 4 := by omega
  have hH := canonical_subset (G := G) U W K
  have hcardU := card_sdiff_add_card_eq_card hH
  have hk := (C3SInput.hub_shape h hK).2.2.2.1
  have hratio := h.card
  have hBU : #(U \ canonical G U W K) = 1 := by omega
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < #(U \ canonical G U W K))
  have hx6 := C3SInput.hub_outside_six h hK hx
  have hxK := C3SInput.hub_outside_reverse h hK hx
  have hxsplit := dg_sdiff_add (G := G) hK.1 x
  have hxle := dg_le_card (G := G) (W \ K) x
  omega

theorem c3s_repair : QB6Assembly.C3SRepair.{u} := by
  intro V _ G _ U W h
  by_cases hno : ∀ T ⊆ W, T.Nonempty → capTheta G U W T ≤ 1
  · exact quartic_of_no_hub h hno
  · push Not at hno
    obtain ⟨T, hT, hne, hp⟩ := hno
    obtain ⟨K, _, hK⟩ := FiniteTests.exists_max_two hT hne (by omega : 2 ≤ capTheta G U W T)
    by_contra hq
    exact not_hub_cover h hK (maximal_cover_of_not_quartic' h hq)

#print axioms quartic_of_uncovered
#print axioms quartic_of_no_hub
#print axioms canonical_hub_intersection
#print axioms petal_signature
#print axioms hub_family_defect
#print axioms hub_family_equality
#print axioms C3SInput.disjoint_hub_big_signature
#print axioms hub_equality_of_cover
#print axioms not_hub_cover
#print axioms c3s_repair
#print c3s_repair
#print QB6Assembly.C3SInput
#print QB6Assembly.Sparse6
#print QB4.Quartic
#print capTheta
#print mixedTheta
#check QB6Assembly.C3SRepair

end Erdos585.QB6C3S
