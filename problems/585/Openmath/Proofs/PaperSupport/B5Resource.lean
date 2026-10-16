import Openmath.Proofs.PaperSupport.B5Defs

/-! The actual original-row intersection resource, parameterized from the
credited C3S positive-part bonus. No linear family or factor is supplied. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.B5
open QB4
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def mixedTheta (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (W X T : Finset V) : ℤ := (q : ℤ) - q * #T + ∑ a ∈ X, row q G W T a

lemma canonical_subset (q : ℕ) (U W T : Finset V) : canonical q G U W T ⊆ U :=
  filter_subset _ _

lemma canonical_mono (q : ℕ) {U W M N : Finset V} (hMN : M ⊆ N) :
    canonical q G U W M ⊆ canonical q G U W N := by
  intro a ha
  obtain ⟨haU, haM⟩ := mem_filter.mp ha
  refine mem_filter.mpr ⟨haU, ?_⟩
  have hd := dg_mono (G := G) hMN a
  unfold row at *
  omega

lemma mixed_le_theta (q : ℕ) {U W X T : Finset V} (hX : X ⊆ U) :
    mixedTheta q G W X T ≤ theta q G U W T := by
  unfold mixedTheta theta
  have h1 : (∑ a ∈ X, row q G W T a) ≤ ∑ a ∈ X, max 0 (row q G W T a) :=
    sum_le_sum fun a _ => le_max_right _ _
  have h2 : (∑ a ∈ X, max 0 (row q G W T a)) ≤ ∑ a ∈ U, max 0 (row q G W T a) :=
    sum_le_sum_of_subset_of_nonneg hX fun a _ _ => le_max_left _ _
  linarith

lemma mixed_canonical (q : ℕ) (U W T : Finset V) :
    mixedTheta q G W (canonical q G U W T) T = theta q G U W T := by
  have hsum : (∑ a ∈ canonical q G U W T, row q G W T a) =
      ∑ a ∈ U, max 0 (row q G W T a) := by
    rw [canonical, sum_filter]
    apply sum_congr rfl
    intro a _
    split_ifs with h
    · exact (max_eq_right (le_of_lt h)).symm
    · exact (max_eq_left (le_of_not_gt h)).symm
  simp only [mixedTheta, theta, hsum]

lemma row_sum (q : ℕ) (W X T : Finset V) :
    (∑ a ∈ X, row q G W T a) =
      (ec G X T : ℤ) - (ec G X W : ℤ) + q * #X := by
  simp [row, sum_add_distrib, sum_sub_distrib, ec, Nat.cast_sum,
    sum_const, mul_comm]

lemma deficiency_eq (D : ℤ) (W X : Finset V) :
    deficiency D G W X = D * #X - (ec G X W : ℤ) := by
  unfold deficiency ec
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.cast_sum]
  ring

lemma deficiency_nonneg (D : ℤ) {W X : Finset V}
    (hcap : ∀ a ∈ X, (dg G W a : ℤ) ≤ D) : 0 ≤ deficiency D G W X :=
  sum_nonneg fun a ha => sub_nonneg.mpr (hcap a ha)

lemma deficiency_le_subset (D : ℤ) {W X U : Finset V}
    (hX : X ⊆ U) (hcap : ∀ a ∈ U, (dg G W a : ℤ) ≤ D) :
    deficiency D G W X ≤ deficiency D G W U :=
  sum_le_sum_of_subset_of_nonneg hX fun a ha _ => sub_nonneg.mpr (hcap a ha)

lemma mixed_potential (q : ℕ) (W X T : Finset V) :
    2 * mixedTheta q G W X T =
      2 * (q : ℤ) + 2 * ((#X : ℤ) - #T) +
      2 * deficiency (2 * (q : ℤ) - 2) G W X -
      potential (2 * (q : ℤ) - 2) G X T := by
  rw [mixedTheta, row_sum, deficiency_eq]
  unfold potential
  ring

lemma cut_mixed_identity (q : ℕ) {U W A C : Finset V}
    (hcard : #W = #U + 1) (hA : A ⊆ W) (hC : C ⊆ U) :
    mixedTheta q G W (U \ C) (W \ A) =
      q * ((#A : ℤ) - #C) - (ec G A (U \ C) : ℤ) := by
  have hcA := card_sdiff_add_card_eq_card hA
  have hcC := card_sdiff_add_card_eq_card hC
  have he := ec_sdiff_add_right (G := G) hA (U \ C)
  have hecomm := ec_comm (G := G) (U \ C) A
  zify at hcard hcA hcC he hecomm
  rw [mixedTheta, row_sum]
  nlinarith

lemma positive_part_supermod (a b c d r : ℤ) (hs : a + b = c + d)
    (hca : c ≤ a) (hcb : c ≤ b) :
    max 0 (a-r) + max 0 (b-r) ≤ max 0 (c-r) + max 0 (d-r) := by
  omega

def bonus (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (W M N : Finset V) (a : V) : ℤ :=
  max 0 (row q G W (M ∪ N) a) + max 0 (row q G W (M ∩ N) a) -
    max 0 (row q G W M a) - max 0 (row q G W N a)

lemma bonus_nonneg (q : ℕ) (W M N : Finset V) (a : V) :
    0 ≤ bonus q G W M N a := by
  have hs := dg_union_add_dg_inter (G := G) M N a
  have h1 := dg_mono (G := G) (inter_subset_left : M ∩ N ⊆ M) a
  have h2 := dg_mono (G := G) (inter_subset_right : M ∩ N ⊆ N) a
  zify at hs h1 h2
  have hh := positive_part_supermod (dg G M a) (dg G N a) (dg G (M ∩ N) a)
    (dg G (M ∪ N) a) ((dg G W a : ℤ)-q) (by omega) h1 h2
  unfold bonus row
  omega

lemma bonus_sum (q : ℕ) (U W M N : Finset V) :
    (∑ a ∈ U, bonus q G W M N a) =
      theta q G U W (M ∪ N) + theta q G U W (M ∩ N) -
        theta q G U W M - theta q G U W N := by
  have hc := card_union_add_card_inter M N
  zify at hc
  simp only [bonus, sum_sub_distrib, sum_add_distrib, theta]
  nlinarith

lemma bonus_shared (q : ℕ) {U W M N : Finset V} {a : V}
    (ha : a ∈ canonical q G U W M ∩ canonical q G U W N) :
    bonus q G W M N a = max 0 (((dg G W a : ℤ)-q) - dg G (M ∩ N) a) := by
  obtain ⟨ham, han⟩ := mem_inter.mp ha
  have hm := (mem_filter.mp ham).2
  have hn := (mem_filter.mp han).2
  have hs := dg_union_add_dg_inter (G := G) M N a
  have h1 := dg_mono (G := G) (inter_subset_left : M ∩ N ⊆ M) a
  have h2 := dg_mono (G := G) (inter_subset_right : M ∩ N ⊆ N) a
  zify at hs h1 h2
  unfold bonus row at *
  omega

/- -/
theorem intersection_budget (q : ℕ) (U W M N : Finset V) :
    (∑ a ∈ canonical q G U W M ∩ canonical q G U W N,
      max 0 (((dg G W a : ℤ)-q) - dg G (M ∩ N) a)) ≤
    theta q G U W (M ∪ N) + theta q G U W (M ∩ N) -
      theta q G U W M - theta q G U W N := by
  have hsub : canonical q G U W M ∩ canonical q G U W N ⊆ U :=
    inter_subset_left.trans (canonical_subset q U W M)
  calc
    _ = ∑ a ∈ canonical q G U W M ∩ canonical q G U W N, bonus q G W M N a :=
      sum_congr rfl fun a ha => (bonus_shared q ha).symm
    _ ≤ ∑ a ∈ U, bonus q G W M N a :=
      sum_le_sum_of_subset_of_nonneg hsub fun a _ _ => bonus_nonneg q W M N a
    _ = _ := bonus_sum q U W M N

theorem r1_original : R1Claim (G := G) := by
  intro q _ U W M N _
  exact intersection_budget q U W M N

theorem theta_supermod (q : ℕ) (U W M N : Finset V) :
    theta q G U W M + theta q G U W N ≤
      theta q G U W (M ∪ N) + theta q G U W (M ∩ N) := by
  have hb := intersection_budget (G := G) q U W M N
  have hn : 0 ≤ ∑ a ∈ canonical q G U W M ∩ canonical q G U W N,
      max 0 (((dg G W a : ℤ)-q) - dg G (M ∩ N) a) :=
    sum_nonneg fun _ _ => le_max_left _ _
  linarith

#print axioms r1_original
#print axioms intersection_budget
#print axioms cut_mixed_identity
end Erdos585.B5
