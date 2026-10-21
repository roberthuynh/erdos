import L34.Main
import NEQAssembly.Components

/-! Original unequal-shore branches for the 3q − 32 theorem (H49).
The endpoint derives one common original omission and one original
unit-edge q-factor; helpers supply no factor premise. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.H3Unequal
open QB4 B5 L34
universe u

/-- Literal original source contract. No selected support or factor is supplied. -/
structure OriginalInput (q j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop where
  q_large : 512 ≤ q
  branch : j = 1 ∨ j = 2
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  card : #B = #A + j
  order : 2 * q ≤ Fintype.card V
  min_degree : ∀ v : V, q ≤ G.degree v
  cap_degree : ∀ v : V, G.degree v ≤ 2 * q - 2
  edges : G.edgeSet.ncard + (3 * q - 32) = (q - 1) * Fintype.card V
  proper : ∀ X : Finset V, 3 ≤ #X → #X < Fintype.card V →
    3 * (q : ℤ) - 31 ≤ ((q : ℤ) - 1) * #X -
      ((G.induce (X : Set V)).edgeSet.ncard : ℤ)

/-- The full original conclusion, stated as a proposition.
FactorOn expands to actual original capacity-one adjacent pairs and full quotas. -/
def H3UnequalClaim : Prop :=
  ∀ (q j : ℕ), ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (A B : Finset V),
    OriginalInput q j G A B →
    ∃ O : Finset V, O ⊆ B ∧ #O = j ∧ FactorOn q G A (B \ O) ∧
      ∃ H : G.Subgraph, H.verts = (↑(A ∪ (B \ O)) : Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Internally derived paired form of exactly the original HC49 resources. -/
structure Input (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Prop where
  q_large : 512 ≤ q
  branch : j = 1 ∨ j = 2
  disjoint : Disjoint A B
  card : #B = #A + j
  minA : ∀ a ∈ A, q ≤ dg G B a
  capA : ∀ a ∈ A, dg G B a ≤ 2 * q - 2
  minB : ∀ b ∈ B, q ≤ dg G A b
  capB : ∀ b ∈ B, dg G A b ≤ 2 * q - 2
  deficient : deficiency (2 * (q : ℤ) - 2) G B A =
    3 * (q : ℤ) - 32 - ((q : ℤ) - 1) * j
  sparse : ∀ X ⊆ A, ∀ Y ⊆ B, 3 ≤ #X + #Y → #X + #Y < #A + #B →
    6 * (q : ℤ) - 62 ≤ potential (2 * (q : ℤ) - 2) G X Y

/-- H1: one SAME original omission pays every original quota cut. -/
theorem factor_of_common_omission (q j : ℕ) {A B O : Finset V}
    (hcard : #B = #A + j) (hO : O ⊆ B) (hOj : #O = j)
    (hgood : ∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0) :
    FactorOn q G A (B \ O) := by
  have hretained : #(B \ O) = #A := by
    have hc := card_sdiff_add_card_eq_card hO
    omega
  have hcut : ∀ X ⊆ B \ O, ∀ Y ⊆ A,
      q * #X ≤ ec G X (A \ Y) + q * #Y := by
    intro X hX Y hY
    have hXB : X ⊆ B := hX.trans sdiff_subset
    have hOT : O ⊆ B \ X := by
      intro v hv
      refine mem_sdiff.mpr ⟨hO hv, ?_⟩
      intro hvX
      exact (mem_sdiff.mp (hX hvX)).2 hv
    have hg := hgood (B \ X) sdiff_subset hOT
    have hm := mixed_le_theta (G := G) q (W := B) (T := B \ X)
      (sdiff_subset : A \ Y ⊆ A)
    have hi : mixedTheta q G B (A \ Y) (B \ X) - q + (q : ℤ) * j =
        q * ((#X : ℤ) - #Y) - (ec G X (A \ Y) : ℤ) := by
      have hcX := card_sdiff_add_card_eq_card hXB
      have hcY := card_sdiff_add_card_eq_card hY
      have he := ec_sdiff_add_right (G := G) hXB (A \ Y)
      have hcomm := ec_comm (G := G) (A \ Y) X
      zify at hcard hcX hcY he hcomm
      rw [mixedTheta, row_sum]
      nlinarith
    have hz : (q : ℤ) * #X ≤ (ec G X (A \ Y) : ℤ) + q * #Y := by
      unfold thetaJ at hg
      nlinarith
    exact_mod_cast hz
  exact FactorOn.swap
    (B5Factor.exists_target_factor (k := q) (B \ O) A hretained hcut)

/-- H1 transport: the SAME actual original pair witness spans both retained shores. -/
theorem factor_exact_subgraph [Fintype V] {q : ℕ} {A W : Finset V}
    (hq : 0 < q) (hA : A.Nonempty) (hAW : Disjoint A W)
    (hfactor : FactorOn q G A W) :
    ∃ H : G.Subgraph, H.verts = (↑(A ∪ W) : Set V) ∧
      H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  obtain ⟨F, hF, hadj, hP, hQ⟩ := hfactor
  have hFA : ∀ x ∈ F, x.1 ∈ A := fun x hx => (mem_product.mp (hF hx)).1
  have hFW : ∀ x ∈ F, x.2 ∈ W := fun x hx => (mem_product.mp (hF hx)).2
  let H := pairSubgraph F hadj
  have hverts : H.verts = (↑(A ∪ W) : Set V) := by
    ext a
    change (∃ x ∈ F, x.1 = a ∨ x.2 = a) ↔ a ∈ A ∪ W
    constructor
    · rintro ⟨x, hx, hxa | hxa⟩
      · exact mem_union_left _ (hxa ▸ hFA x hx)
      · exact mem_union_right _ (hxa ▸ hFW x hx)
    · intro ha
      rcases mem_union.mp ha with ha | ha
      · have hc : 0 < #{x ∈ F | x.1 = a} := by rw [hP a ha]; exact hq
        obtain ⟨x, hx⟩ := card_pos.mp hc
        exact ⟨x, (mem_filter.mp hx).1, Or.inl (mem_filter.mp hx).2⟩
      · have hc : 0 < #{x ∈ F | x.2 = a} := by rw [hQ a ha]; exact hq
        obtain ⟨x, hx⟩ := card_pos.mp hc
        exact ⟨x, (mem_filter.mp hx).1, Or.inr (mem_filter.mp hx).2⟩
  have hdeg : ∀ a ∈ H.verts, ∀ [Fintype (H.neighborSet a)], H.degree a = q := by
    rintro a ⟨x, hx, rfl | rfl⟩ _
    · rw [degree_pairSubgraph_left hadj hFW (Finset.disjoint_left.mp hAW (hFA x hx))]
      exact hP x.1 (hFA x hx)
    · rw [degree_pairSubgraph_right hadj hFA (Finset.disjoint_right.mp hAW (hFW x hx))]
      exact hQ x.2 (hFW x hx)
  refine ⟨H, hverts, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hA
    rw [hverts]
    exact ⟨a, mem_union_left _ ha⟩
  · intro a
    rw [SimpleGraph.Subgraph.coe_degree]
    exact hdeg a a.2

/-- Half the original paired potential, with integer coefficients. -/
def coreDefect (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) : ℤ := ((q : ℤ) - 1) * (#X + #Y) - ec G X Y

omit [DecidableEq V] in
lemma twice_coreDefect (q : ℕ) (X Y : Finset V) :
    2 * coreDefect q G X Y = potential (2 * (q : ℤ) - 2) G X Y := by
  unfold coreDefect potential
  ring

namespace Input
variable {q j : ℕ} {A B : Finset V}

omit [DecidableEq V] in
lemma capA_int (h : Input q j G A B) {a : V} (ha : a ∈ A) :
    (dg G B a : ℤ) ≤ 2 * (q : ℤ) - 2 := by
  have hd := h.capA a ha
  have hq := h.q_large
  omega

omit [DecidableEq V] in
lemma capB_int (h : Input q j G A B) {b : V} (hb : b ∈ B) :
    (dg G A b : ℤ) ≤ 2 * (q : ℤ) - 2 := by
  have hd := h.capB b hb
  have hq := h.q_large
  omega

lemma scar_nonneg (h : Input q j G A B) {X : Finset V} (hX : X ⊆ A) :
    0 ≤ deficiency (2 * (q : ℤ) - 2) G B X :=
  deficiency_nonneg _ fun _a ha => h.capA_int (hX ha)

lemma scar_le (h : Input q j G A B) {X : Finset V} (hX : X ⊆ A) :
    deficiency (2 * (q : ℤ) - 2) G B X ≤
      3 * (q : ℤ) - 32 - ((q : ℤ) - 1) * j := by
  calc _ ≤ deficiency (2 * (q : ℤ) - 2) G B A :=
      deficiency_le_subset _ hX fun a ha => h.capA_int ha
    _ = _ := h.deficient

lemma scar_split (h : Input q j G A B) {X : Finset V} (hX : X ⊆ A) :
    deficiency (2 * (q : ℤ) - 2) G B (A \ X) +
      deficiency (2 * (q : ℤ) - 2) G B X =
      3 * (q : ℤ) - 32 - ((q : ℤ) - 1) * j := by
  rw [← h.deficient]
  exact sum_sdiff hX

lemma row_scar_le (h : Input q j G A B) {a : V} (ha : a ∈ A) :
    2 * (q : ℤ) - 2 - dg G B a ≤
      3 * (q : ℤ) - 32 - ((q : ℤ) - 1) * j := by
  have hs := h.scar_le (singleton_subset_iff.mpr ha)
  simpa [deficiency] using hs

omit [DecidableEq V] in
lemma shores_large (h : Input q j G A B) : q ≤ #A ∧ q + j ≤ #B := by
  have hbn : B.Nonempty := card_pos.mp (by have hc := h.card; rcases h.branch with hj | hj <;> omega)
  obtain ⟨b, hb⟩ := hbn
  have hd := h.minB b hb
  have hc := dg_le_card (G := G) A b
  have hi := h.card
  omega

omit [DecidableEq V] in
lemma theta_full (h : Input q j G A B) : thetaJ q j G A B B = 0 := by
  simp only [thetaJ, theta, row, sub_self, zero_add,
    max_eq_right (Nat.cast_nonneg q), sum_const, nsmul_eq_mul]
  rw [h.card]
  push_cast
  ring

omit [DecidableEq V] in
lemma theta_empty (h : Input q j G A B) : thetaJ q j G A B ∅ = (q : ℤ) * j := by
  have hz : ∀ a ∈ A, max 0 (row q G B ∅ a) = 0 := by
    intro a ha
    have hm := h.minA a ha
    have he : dg G ∅ a = 0 := by simp [dg]
    rw [row, he]
    simp only [Nat.cast_zero, zero_sub]
    omega
  simp only [thetaJ, theta, card_empty, Nat.cast_zero, mul_zero, sub_zero]
  rw [sum_eq_zero hz]
  ring

lemma theta_supermod (q j : ℕ) (A B T U : Finset V) :
    thetaJ q j G A B T + thetaJ q j G A B U ≤
      thetaJ q j G A B (T ∪ U) + thetaJ q j G A B (T ∩ U) := by
  have hh := B5.theta_supermod (G := G) q A B T U
  unfold thetaJ
  linarith

omit [DecidableEq V] in
/-- H2: the direct small-test bound uses no proper-support floor. -/
lemma theta_small_bound (h : Input q j G A B) {T : Finset V}
    (hsize : #T ≤ q - 2) :
    thetaJ q j G A B T ≤ 3 * (q : ℤ) - 32 + j - q * #T := by
  have hq := h.q_large
  have hphi : ∀ a ∈ A, max 0 (row q G B T a) ≤ 2 * (q : ℤ) - 2 - dg G B a := by
    intro a ha
    have hd := dg_le_card (G := G) T a
    have hc := h.capA_int ha
    unfold row
    omega
  have hsum : (∑ a ∈ A, max 0 (row q G B T a)) ≤
      3 * (q : ℤ) - 32 - ((q : ℤ) - 1) * j := by
    calc _ ≤ deficiency (2 * (q : ℤ) - 2) G B A := sum_le_sum hphi
      _ = _ := h.deficient
  unfold thetaJ theta
  nlinarith

omit [DecidableEq V] in
lemma theta_intermediate (h : Input q j G A B) {T : Finset V}
    (hlo : 3 ≤ #T) (hhi : #T ≤ q - 2) : thetaJ q j G A B T ≤ -30 := by
  have hh := h.theta_small_bound hhi
  have hj : (j : ℤ) ≤ 2 := by rcases h.branch with hj | hj <;> omega
  have hp : 0 ≤ (q : ℤ) * ((#T : ℤ) - 3) :=
    mul_nonneg (Nat.cast_nonneg _) (by omega)
  nlinarith

lemma minA_two (h : Input q 2 G A B) {a : V} (ha : a ∈ A) :
    q + 28 ≤ dg G B a := by
  have hs := h.row_scar_le ha
  norm_num at hs
  omega

lemma theta_tiny_two (h : Input q 2 G A B) {T : Finset V} (hsize : #T ≤ 2) :
    thetaJ q 2 G A B T = 2 * (q : ℤ) - q * #T := by
  have hz : ∀ a ∈ A, max 0 (row q G B T a) = 0 := by
    intro a ha
    have hd := dg_le_card (G := G) T a
    have hm := h.minA_two ha
    unfold row
    omega
  unfold thetaJ theta
  rw [sum_eq_zero hz]
  ring

omit [DecidableEq V] in
lemma theta_singleton_one (h : Input q 1 G A B) {T : Finset V} (ht : #T = 1) :
    thetaJ q 1 G A B T ≤ 1 := by
  have hq := h.q_large
  have hrow : ∀ a ∈ A, ((q : ℤ) - 2) * max 0 (row q G B T a) ≤
      2 * (q : ℤ) - 2 - dg G B a := by
    intro a ha
    have hd := dg_le_card (G := G) T a
    have hm := h.minA a ha
    have hc := h.capA_int ha
    by_cases hz : max 0 (row q G B T a) = 0
    · rw [hz, mul_zero]; omega
    · have hp : max 0 (row q G B T a) = 1 := by unfold row at *; omega
      have he : dg G B a = q := by unfold row at *; omega
      rw [hp, he]
      linarith
  have hs : ((q : ℤ) - 2) * (∑ a ∈ A, max 0 (row q G B T a)) ≤ 2 * q - 31 := by
    rw [mul_sum]
    calc _ ≤ deficiency (2 * (q : ℤ) - 2) G B A := sum_le_sum hrow
      _ = _ := by rw [h.deficient]; ring
  have hn : 0 ≤ ∑ a ∈ A, max 0 (row q G B T a) :=
    sum_nonneg fun _ _ => le_max_left _ _
  have hle : (∑ a ∈ A, max 0 (row q G B T a)) ≤ 1 := by
    by_contra! hbad
    have hp := mul_nonneg (show 0 ≤ (q : ℤ) - 2 by omega) (show 0 ≤ (∑ a ∈ A, max 0 (row q G B T a)) - 2 by omega)
    nlinarith
  unfold thetaJ theta
  rw [ht]
  norm_num
  linarith

omit [DecidableEq V] in
lemma theta_pair_one (h : Input q 1 G A B) {T : Finset V} (ht : #T = 2) :
    thetaJ q 1 G A B T ≤ 0 := by
  have hq := h.q_large
  have hrow : ∀ a ∈ A, ((q : ℤ) - 3) * max 0 (row q G B T a) ≤
      2 * (2 * (q : ℤ) - 2 - dg G B a) := by
    intro a ha
    have hd := dg_le_card (G := G) T a
    have hm := h.minA a ha
    have hc := h.capA_int ha
    by_cases hz : max 0 (row q G B T a) = 0
    · rw [hz, mul_zero]; omega
    · have hp : max 0 (row q G B T a) = 1 ∨ max 0 (row q G B T a) = 2 := by unfold row at *; omega
      rcases hp with hp | hp
      · have hdeg : (dg G B a : ℤ) ≤ q + 1 := by unfold row at hp; omega
        rw [hp]
        nlinarith
      · have hdeg : (dg G B a : ℤ) = q := by unfold row at hp; omega
        rw [hp]
        nlinarith
  have hs : ((q : ℤ) - 3) * (∑ a ∈ A, max 0 (row q G B T a)) ≤ 2 * (2 * q - 31) := by
    rw [mul_sum]
    calc _ ≤ ∑ a ∈ A, 2 * (2 * (q : ℤ) - 2 - dg G B a) := sum_le_sum hrow
      _ = 2 * deficiency (2 * (q : ℤ) - 2) G B A := by unfold deficiency; rw [mul_sum]
      _ = _ := by rw [h.deficient]; ring
  have hle : (∑ a ∈ A, max 0 (row q G B T a)) ≤ 3 := by
    by_contra! hbad
    have hp := mul_nonneg (show 0 ≤ (q : ℤ) - 3 by omega) (show 0 ≤ (∑ a ∈ A, max 0 (row q G B T a)) - 4 by omega)
    nlinarith
  unfold thetaJ theta
  rw [ht]
  norm_num
  linarith

lemma theta_tiny_le (h : Input q j G A B) {T : Finset V} (hsize : #T ≤ 2) :
    thetaJ q j G A B T ≤ 2 * q := by
  rcases h.branch with hj | hj
  · subst j
    have hcases : #T = 0 ∨ #T = 1 ∨ #T = 2 := by omega
    rcases hcases with ht | ht | ht
    · have he : T = ∅ := card_eq_zero.mp ht
      rw [he, h.theta_empty]
      norm_num
      omega
    · have hs := h.theta_singleton_one ht
      have hq := h.q_large
      omega
    · have hs := h.theta_pair_one ht
      omega
  · subst j
    rw [h.theta_tiny_two hsize]
    have hn := mul_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg #T : (0 : ℤ) ≤ #T)
    linarith

omit [DecidableEq V] in
lemma edge_cap_T (h : Input q j G A B) {X T : Finset V} (hX : X ⊆ A) (hT : T ⊆ B) :
    (ec G X T : ℤ) ≤ (2 * (q : ℤ) - 2) * #T := by
  rw [ec_comm, ec, Nat.cast_sum]
  calc
    _ ≤ ∑ _b ∈ T, (2 * (q : ℤ) - 2) := by
      refine sum_le_sum fun b hb => ?_
      have hd := dg_mono (G := G) hX b
      have hc := h.capB_int (hT hb)
      omega
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

lemma canonical_proper (h : Input q j G A B) {T : Finset V}
    (hT : T ⊆ B) (hp : 0 < thetaJ q j G A B T) : canonical q G A B T ≠ A := by
  intro heq
  have hc := card_sdiff_add_card_eq_card hT
  have he := ec_sdiff_add_right (G := G) hT A
  have hm := Bq.ec_lower_of_min (G := G) (sdiff_subset : B \ T ⊆ B) h.minB
  rw [ec_comm] at hm
  have hi := thetaJ_canonical (G := G) q j A B T
  rw [heq, row_sum] at hi
  have hcard := h.card
  zify at hc he hm hcard
  nlinarith

/-- H2 large cores pay both the proper floor and the exact outside-scar account. -/
lemma positive_shape (h : Input q j G A B) {T : Finset V}
    (hT : T ⊆ B) (hlarge : q - 1 ≤ #T) (hp : 0 < thetaJ q j G A B T) :
    let C := canonical q G A B T
    let k : ℤ := (#C : ℤ) - #T
    let ε := coreDefect q G C T - (3 * q - 31)
    #T < #B ∧ #C < #A ∧ 1 - (j : ℤ) ≤ k ∧ k ≤ 2 ∧
      thetaJ q j G A B T ≤ j + 1 ∧ 0 ≤ ε ∧
      ε + deficiency (2 * (q : ℤ) - 2) G B (A \ C) =
        j + k - thetaJ q j G A B T - 1 := by
  dsimp only
  let C := canonical q G A B T
  let k : ℤ := (#C : ℤ) - #T
  let a := deficiency (2 * (q : ℤ) - 2) G B C
  have hCU : C ⊆ A := canonical_subset q A B T
  have hq := h.q_large
  have hj : (j : ℤ) ≤ 2 := by rcases h.branch with hj | hj <;> omega
  have htw : T ≠ B := fun heq => by subst T; have hf := h.theta_full; omega
  have hlt : #T < #B := card_lt_card ⟨hT, fun hh => htw (Subset.antisymm hT hh)⟩
  have hclt : #C < #A := card_lt_card ⟨hCU, fun hh => h.canonical_proper hT hp (Subset.antisymm hCU hh)⟩
  have hal := h.scar_le hCU
  have han := h.scar_nonneg hCU
  have hbound : thetaJ q j G A B T ≤ (q : ℤ) * ((j : ℤ) + k) := by
    rw [thetaJ_canonical]
    have hs : (∑ b ∈ C, row q G B T b) ≤ (q : ℤ) * #C := by
      calc
        _ ≤ ∑ _b ∈ C, (q : ℤ) := by
          refine sum_le_sum fun b _ => ?_
          have hd := dg_mono (G := G) hT b
          unfold row
          omega
        _ = _ := by simp [mul_comm]
    dsimp [k]
    nlinarith
  have hk0 : 1 - (j : ℤ) ≤ k := by
    by_contra! hbad
    have hh := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg q) (show (j : ℤ) + k ≤ 0 by omega)
    linarith
  have hsp := h.sparse C hCU T hT (by omega) (by omega)
  have hi := thetaJ_potential (G := G) q j A B T
  have hik : 2 * thetaJ q j G A B T = 2 * (q : ℤ) * j + 2 * k + 2 * a -
      potential (2 * (q : ℤ) - 2) G C T := hi
  have hlow : thetaJ q j G A B T ≤ (j : ℤ) + k - 1 := by dsimp [a] at hik; nlinarith
  have he := h.edge_cap_T hCU hT
  have hg : (2 * (q : ℤ) - 2) * k ≤ potential (2 * (q : ℤ) - 2) G C T := by
    dsimp [k]
    unfold potential
    nlinarith
  have hk2 : k ≤ 2 := by
    by_contra! hbad
    have hprod : 0 ≤ ((q : ℤ) - 2) * (k - 3) := mul_nonneg (by omega) (by omega)
    dsimp [a] at hik
    nlinarith
  have hε : 0 ≤ coreDefect q G C T - (3 * q - 31) := by
    have hh := twice_coreDefect (G := G) q C T
    omega
  have hsplit := h.scar_split hCU
  have hidentity : coreDefect q G C T - (3 * q - 31) +
      deficiency (2 * (q : ℤ) - 2) G B (A \ C) =
      j + k - thetaJ q j G A B T - 1 := by
    have hh := twice_coreDefect (G := G) q C T
    dsimp [a] at hik
    nlinarith
  exact ⟨hlt, hclt, hk0, hk2, by omega, hε, hidentity⟩

lemma outside_scar_le (h : Input q j G A B) {T : Finset V}
    (hT : T ⊆ B) (hlarge : q - 1 ≤ #T) (hp : 0 < thetaJ q j G A B T) :
    deficiency (2 * (q : ℤ) - 2) G B (A \ canonical q G A B T) ≤ j := by
  have hs := h.positive_shape hT hlarge hp
  dsimp only at hs
  omega

lemma canonical_internal_min (h : Input q j G A B) {T : Finset V}
    (hT : T ⊆ B) (hlarge : q - 1 ≤ #T) (hp : 0 < thetaJ q j G A B T)
    {a : V} (ha : a ∈ canonical q G A B T) :
    (q : ℤ) - 1 - (coreDefect q G (canonical q G A B T) T - (3 * q - 31)) ≤
      dg G T a := by
  have hs := h.positive_shape hT hlarge hp
  dsimp only at hs
  have hCU := canonical_subset (G := G) q A B T
  have hq := h.q_large
  have hsp := h.sparse ((canonical q G A B T).erase a)
    ((erase_subset _ _).trans hCU) T hT (by omega)
    (by have hc := card_le_card (erase_subset a (canonical q G A B T)); omega)
  have hi := potential_erase_left (G := G) (2 * (q : ℤ) - 2) ha T
  have hh := twice_coreDefect (G := G) q (canonical q G A B T) T
  rw [hi] at hsp
  omega

lemma canonical_internal_min_coarse (h : Input q j G A B) {T : Finset V}
    (hT : T ⊆ B) (hlarge : q - 1 ≤ #T) (hp : 0 < thetaJ q j G A B T)
    {a : V} (ha : a ∈ canonical q G A B T) : q - 3 ≤ dg G T a := by
  have hi := h.canonical_internal_min hT hlarge hp ha
  have hs := h.positive_shape hT hlarge hp
  dsimp only at hs
  have ho := h.scar_nonneg (sdiff_subset : A \ canonical q G A B T ⊆ A)
  have hj := h.branch
  rcases hj with hj | hj <;> omega

lemma theta_large_le (h : Input q j G A B) {T : Finset V}
    (hT : T ⊆ B) (hlarge : q - 1 ≤ #T) : thetaJ q j G A B T ≤ j + 1 := by
  by_cases hp : 0 < thetaJ q j G A B T
  · have hs := h.positive_shape hT hlarge hp
    dsimp only at hs
    exact hs.2.2.2.2.1
  · omega

lemma scar_intersection_lower (h : Input q j G A B) {T U : Finset V}
    (hT : T ⊆ B) (hTl : q - 1 ≤ #T) (hTp : 0 < thetaJ q j G A B T)
    (hU : U ⊆ B) (hUl : q - 1 ≤ #U) (hUp : 0 < thetaJ q j G A B U) :
    (q : ℤ) - 34 ≤ deficiency (2 * (q : ℤ) - 2) G B
      (canonical q G A B T ∩ canonical q G A B U) := by
  have ht := h.outside_scar_le hT hTl hTp
  have hu := h.outside_scar_le hU hUl hUp
  have hst := h.scar_split (canonical_subset (G := G) q A B T)
  have hsu := h.scar_split (canonical_subset (G := G) q A B U)
  have hl := h.scar_le (union_subset (canonical_subset (G := G) q A B T)
    (canonical_subset (G := G) q A B U))
  have hi : deficiency (2 * (q : ℤ) - 2) G B
        (canonical q G A B T ∪ canonical q G A B U) +
      deficiency (2 * (q : ℤ) - 2) G B
        (canonical q G A B T ∩ canonical q G A B U) =
      deficiency (2 * (q : ℤ) - 2) G B (canonical q G A B T) +
      deficiency (2 * (q : ℤ) - 2) G B (canonical q G A B U) := by
    exact sum_union_inter
  rcases h.branch with hj | hj <;> rw [hj] at ht hu hst hsu hl <;> norm_num at * <;> omega

/-- H3 uses the actual shared rows and the original convex-gap budget. -/
lemma large_intersection (h : Input q j G A B) {T U : Finset V}
    (hT : T ⊆ B) (hTl : q - 1 ≤ #T) (hTp : 0 < thetaJ q j G A B T)
    (hU : U ⊆ B) (hUl : q - 1 ≤ #U) (hUp : 0 < thetaJ q j G A B U) :
    q - 1 ≤ #(T ∩ U) := by
  have hq := h.q_large
  have hj : (j : ℤ) ≤ 2 := by rcases h.branch with hj | hj <;> omega
  have hcup := h.theta_large_le (union_subset hT hU)
    (hTl.trans (card_le_card subset_union_left))
  by_contra! hbad
  have hsmall : #(T ∩ U) ≤ q - 2 := by omega
  by_cases htiny : #(T ∩ U) ≤ 2
  · let M := canonical q G A B T ∩ canonical q G A B U
    have hscarlo := h.scar_intersection_lower hT hTl hTp hU hUl hUp
    change (q : ℤ) - 34 ≤ deficiency (2 * (q : ℤ) - 2) G B M at hscarlo
    have hdeg : ∀ a ∈ M, 2 * (q : ℤ) - 8 ≤ dg G B a := by
      intro a ha
      obtain ⟨hat, hau⟩ := mem_inter.mp ha
      have hdt := h.canonical_internal_min_coarse hT hTl hTp hat
      have hdu := h.canonical_internal_min_coarse hU hUl hUp hau
      have hid := dg_union_add_dg_inter (G := G) T U a
      have hd := dg_mono (G := G) (union_subset hT hU) a
      have hdi := dg_le_card (G := G) (T ∩ U) a
      omega
    have hscarhi : deficiency (2 * (q : ℤ) - 2) G B M ≤ 6 * #M := by
      calc
        _ ≤ ∑ _a ∈ M, (6 : ℤ) := by
          apply sum_le_sum
          intro a ha
          have hd := hdeg a ha
          omega
        _ = _ := by simp [mul_comm]
    have hgap : ((#M : ℤ) * ((q : ℤ) - 10)) ≤
        ∑ a ∈ M, max 0 (((dg G B a : ℤ) - q) - dg G (T ∩ U) a) := by
      calc
        _ = ∑ _a ∈ M, ((q : ℤ) - 10) := by simp only [sum_const, nsmul_eq_mul]
        _ ≤ _ := by
          apply sum_le_sum
          intro a ha
          have hd := hdeg a ha
          have hdi := dg_le_card (G := G) (T ∩ U) a
          omega
    have hbudget := intersection_budget (G := G) q A B T U
    have hit := h.theta_tiny_le htiny
    have hbudgetJ : (∑ a ∈ M, max 0 (((dg G B a : ℤ) - q) - dg G (T ∩ U) a)) ≤
        thetaJ q j G A B (T ∪ U) + thetaJ q j G A B (T ∩ U) -
          thetaJ q j G A B T - thetaJ q j G A B U := by
      unfold thetaJ
      change (∑ a ∈ M, max 0 (((dg G B a : ℤ) - q) - dg G (T ∩ U) a)) ≤ _ at hbudget
      linarith
    have hmul : 0 ≤ ((6 : ℤ) * #M - ((q : ℤ) - 34)) * ((q : ℤ) - 10) :=
      mul_nonneg (by omega) (by omega)
    have hpoly : 0 ≤ ((q : ℤ) - 512) * ((q : ℤ) + 456) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  · have hinter := h.theta_intermediate (by omega) hsmall
    have hsuper := theta_supermod (G := G) q j A B T U
    omega

end Input

/-- An actual large positive original cut; tiny singletons are handled separately. -/
def LargePositive (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B T : Finset V) : Prop :=
  T ⊆ B ∧ q - 1 ≤ #T ∧ 0 < thetaJ q j G A B T

def MaxLargePositive (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B M : Finset V) : Prop :=
  LargePositive q j G A B M ∧
    ∀ N ⊆ B, M ⊆ N → M ≠ N → thetaJ q j G A B N ≤ 0

structure GreatestHigh (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K : Finset V) : Prop where
  positive : LargePositive q j G A B K
  height : ∀ T, LargePositive q j G A B T → thetaJ q j G A B T ≤ thetaJ q j G A B K
  contains_high : ∀ T, LargePositive q j G A B T →
    thetaJ q j G A B T = thetaJ q j G A B K → T ⊆ K

/-- Finite maximal extension, using the entire actual powerset. -/
lemma exists_max_large_extension (q j : ℕ) {A B T : Finset V}
    (hT : LargePositive q j G A B T) :
    ∃ M, T ⊆ M ∧ MaxLargePositive q j G A B M := by
  let F := B.powerset.filter fun M => T ⊆ M ∧ LargePositive q j G A B M
  have hF : F.Nonempty := ⟨T, mem_filter.mpr ⟨mem_powerset.mpr hT.1, Subset.rfl, hT⟩⟩
  obtain ⟨M, hM, hmax⟩ := exists_max_image F Finset.card hF
  obtain ⟨hmB, hTM, hmpos⟩ := mem_filter.mp hM
  refine ⟨M, hTM, hmpos, ?_⟩
  intro N hNB hMN hneMN
  by_contra! hnpos
  have hnF : N ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hNB, hTM.trans hMN,
    hNB, hmpos.2.1.trans (card_le_card hMN), hnpos⟩
  have hle := hmax N hnF
  have hlt : #M < #N := card_lt_card
    ⟨hMN, fun hNM => hneMN (Subset.antisymm hMN hNM)⟩
  omega

/-- H3: the greatest high set is derived, not an input laminarity premise. -/
lemma exists_greatest_high {q j : ℕ} {A B : Finset V} (h : Input q j G A B)
    (hex : ∃ T, LargePositive q j G A B T) : ∃ K, GreatestHigh q j G A B K := by
  let F := B.powerset.filter fun T => LargePositive q j G A B T
  have hF : F.Nonempty := by
    obtain ⟨T, hT⟩ := hex
    exact ⟨T, mem_filter.mpr ⟨mem_powerset.mpr hT.1, hT⟩⟩
  obtain ⟨M, hM, hm⟩ := exists_max_image F (thetaJ q j G A B) hF
  let H := F.filter fun T => thetaJ q j G A B T = thetaJ q j G A B M
  have hH : H.Nonempty := ⟨M, mem_filter.mpr ⟨hM, rfl⟩⟩
  obtain ⟨K, hK, hk⟩ := exists_max_image H Finset.card hH
  obtain ⟨hKF, hKM⟩ := mem_filter.mp hK
  have hKpos : LargePositive q j G A B K := (mem_filter.mp hKF).2
  have hKpositive := hKpos.2.2
  have hheight : ∀ T, LargePositive q j G A B T → thetaJ q j G A B T ≤ thetaJ q j G A B K := by
    intro T hT
    rw [hKM]
    exact hm T (mem_filter.mpr ⟨mem_powerset.mpr hT.1, hT⟩)
  refine ⟨K, hKpos, hheight, ?_⟩
  intro T hT heq
  have hUpos : LargePositive q j G A B (K ∪ T) := by
    have hIlarge := h.large_intersection hKpos.1 hKpos.2.1 hKpos.2.2 hT.1 hT.2.1 hT.2.2
    have hUb := union_subset hKpos.1 hT.1
    have hUl : q - 1 ≤ #(K ∪ T) := hKpos.2.1.trans (card_le_card subset_union_left)
    have hi : thetaJ q j G A B (K ∩ T) ≤ thetaJ q j G A B K := by
      by_cases hip : 0 < thetaJ q j G A B (K ∩ T)
      · exact hheight _ ⟨inter_subset_left.trans hKpos.1, hIlarge, hip⟩
      · omega
    have hsuper := Input.theta_supermod (G := G) q j A B K T
    exact ⟨hUb, hUl, by omega⟩
  have hIlarge := h.large_intersection hKpos.1 hKpos.2.1 hKpos.2.2 hT.1 hT.2.1 hT.2.2
  have hi : thetaJ q j G A B (K ∩ T) ≤ thetaJ q j G A B K := by
    by_cases hip : 0 < thetaJ q j G A B (K ∩ T)
    · exact hheight _ ⟨inter_subset_left.trans hKpos.1, hIlarge, hip⟩
    · omega
  have hu := hheight _ hUpos
  have hs := Input.theta_supermod (G := G) q j A B K T
  have hueq : thetaJ q j G A B (K ∪ T) = thetaJ q j G A B M := by omega
  have hUH : K ∪ T ∈ H := mem_filter.mpr
    ⟨mem_filter.mpr ⟨mem_powerset.mpr hUpos.1, hUpos⟩, hueq⟩
  have hc := hk (K ∪ T) hUH
  have he : K ∪ T = K := (eq_of_subset_of_card_le subset_union_left hc).symm
  simpa only [he] using (subset_union_right : T ⊆ K ∪ T)

lemma GreatestHigh.subset_max {q j : ℕ} {A B K M : Finset V} (h : Input q j G A B)
    (hK : GreatestHigh q j G A B K) (hM : MaxLargePositive q j G A B M) : K ⊆ M := by
  by_contra hn
  have hneq : M ≠ M ∪ K := by
    intro he
    exact hn (by simpa [← he] using (subset_union_right : K ⊆ M ∪ K))
  have hu := hM.2 (M ∪ K) (union_subset hM.1.1 hK.positive.1) subset_union_left hneq
  have hil := h.large_intersection hM.1.1 hM.1.2.1 hM.1.2.2
    hK.positive.1 hK.positive.2.1 hK.positive.2.2
  have hip : 0 < thetaJ q j G A B (M ∩ K) := by
    have hs := Input.theta_supermod (G := G) q j A B M K
    have hm := hM.1.2.2
    have hk := hK.positive.2.2
    omega
  have hi := hK.height _ ⟨inter_subset_left.trans hM.1.1, hil, hip⟩
  have hs := Input.theta_supermod (G := G) q j A B M K
  have hm := hM.1.2.2
  omega

/-- H0 original incidence on disjoint unions, with no induced-support replacement. -/
lemma ec_union_right {X Y : Finset V} (hXY : Disjoint X Y) (Z : Finset V) :
    ec G Z (X ∪ Y) = ec G Z X + ec G Z Y := by
  unfold ec
  simp_rw [dg_union_of_disjoint (G := G) hXY]
  exact sum_add_distrib

lemma ec_union_left {X Y : Finset V} (hXY : Disjoint X Y) (Z : Finset V) :
    ec G (X ∪ Y) Z = ec G X Z + ec G Y Z := by
  rw [ec_comm, ec_union_right hXY, ec_comm (G := G) Z X, ec_comm (G := G) Z Y]

omit [DecidableEq V] in
lemma ec_internal_zero {A B X : Finset V} (hdis : Disjoint A B)
    (hbip : G.IsBipartiteWith (A : Set V) (B : Set V)) (hX : X ⊆ A) :
    ec G X X = 0 := by
  unfold ec
  apply sum_eq_zero
  intro a ha
  unfold dg
  apply card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro b hb
  obtain ⟨hbX, hab⟩ := mem_filter.mp hb
  exact Finset.disjoint_left.mp hdis (hX hbX) (hbip.mem_of_mem_adj (hX ha) hab)

lemma induced_edges_eq_ec [Fintype V] {A B X Y : Finset V}
    (hdis : Disjoint A B) (hbip : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hX : X ⊆ A) (hY : Y ⊆ B) :
    (G.induce (↑(X ∪ Y) : Set V)).edgeSet.ncard = ec G X Y := by
  have hXY := hdis.mono hX hY
  have hx := ec_internal_zero hdis hbip hX
  have hy := ec_internal_zero hdis.symm hbip.symm hY
  have he := NEQAssembly.ec_self_eq_twice_induced_edges (G := G) (X ∪ Y)
  rw [ec_union_left hXY, ec_union_right hXY, ec_union_right hXY, hx, hy,
    ec_comm (G := G) Y X] at he
  omega

namespace OriginalInput
variable [Fintype V] {q j : ℕ} {A B : Finset V}

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma shore_order (h : OriginalInput q j G A B) : #A + #B = Fintype.card V := by
  have hc := card_union_of_disjoint h.disjoint
  rw [h.cover, card_univ] at hc
  exact hc.symm

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- H0: every internal field is derived from the literal original graph fields. -/
theorem to_input (h : OriginalInput q j G A B) :
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    Input q j G A B := by
  classical
  have horder := h.shore_order
  have hq := h.q_large
  refine ⟨h.q_large, h.branch, h.disjoint, h.card, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [dg_eq_degree h.bipartite ha]
    exact h.min_degree a
  · intro a ha
    rw [dg_eq_degree h.bipartite ha]
    exact h.cap_degree a
  · intro b hb
    rw [dg_eq_degree h.bipartite.symm hb]
    exact h.min_degree b
  · intro b hb
    rw [dg_eq_degree h.bipartite.symm hb]
    exact h.cap_degree b
  · rw [deficiency_eq, ec_eq_ncard h.bipartite]
    have he := h.edges
    have hc := h.card
    have hqm : q - 1 + 1 = q := by omega
    have hcm : 3 * q - 32 + 32 = 3 * q := by omega
    zify at he hc horder hqm hcm
    nlinarith
  · intro X hX Y hY hlarge hproper
    have hXY := h.disjoint.mono hX hY
    have hc := card_union_of_disjoint hXY
    have hf := h.proper (X ∪ Y) (by omega) (by omega)
    rw [induced_edges_eq_ec h.disjoint h.bipartite hX hY, hc] at hf
    unfold potential
    push_cast at hf ⊢
    nlinarith

end OriginalInput

/-- The actual original row optimizer; equality rows may be included. -/
structure Optimizer (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K C : Finset V) : Prop where
  subset : C ⊆ A
  inside : ∀ a ∈ C, 0 ≤ row q G B K a
  outside : ∀ a ∈ A \ C, row q G B K a ≤ 0

lemma strict_optimizer (q : ℕ) (A B K : Finset V) :
    Optimizer q G A B K (canonical q G A B K) := by
  refine ⟨canonical_subset q A B K, ?_, ?_⟩
  · intro a ha
    exact le_of_lt (mem_filter.mp ha).2
  · intro a ha
    obtain ⟨haA, haC⟩ := mem_sdiff.mp ha
    by_contra! hp
    exact haC (mem_filter.mpr ⟨haA, hp⟩)

def weakCore (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K : Finset V) : Finset V := A.filter fun a => 0 ≤ row q G B K a

lemma weak_optimizer (q : ℕ) (A B K : Finset V) :
    Optimizer q G A B K (weakCore q G A B K) := by
  refine ⟨filter_subset _ _, fun _ ha => (mem_filter.mp ha).2, ?_⟩
  intro a ha
  have hh : ¬0 ≤ row q G B K a := by
    intro hp
    exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨(mem_sdiff.mp ha).1, hp⟩)
  omega

lemma weak_outside_strict (q : ℕ) (A B K : Finset V) {a : V}
    (ha : a ∈ A \ weakCore q G A B K) : row q G B K a < 0 := by
  have hh : ¬0 ≤ row q G B K a := by
    intro hp
    exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨(mem_sdiff.mp ha).1, hp⟩)
  omega

namespace Optimizer
variable {q j : ℕ} {A B K C : Finset V}

lemma theta_eq (h : Optimizer q G A B K C) :
    thetaJ q j G A B K = (q : ℤ) * j - q * #K + ∑ a ∈ C, row q G B K a := by
  have hs := sum_sdiff h.subset (f := fun a => max 0 (row q G B K a))
  have hout : (∑ a ∈ A \ C, max 0 (row q G B K a)) = 0 :=
    sum_eq_zero fun a ha => max_eq_left (h.outside a ha)
  have hin : (∑ a ∈ C, max 0 (row q G B K a)) = ∑ a ∈ C, row q G B K a :=
    sum_congr rfl fun a ha => max_eq_right (h.inside a ha)
  rw [hout, hin, zero_add] at hs
  unfold thetaJ theta
  rw [← hs]
  ring

lemma theta_potential (h : Optimizer q G A B K C) :
    2 * thetaJ q j G A B K = 2 * (q : ℤ) * j + 2 * ((#C : ℤ) - #K) +
      2 * deficiency (2 * (q : ℤ) - 2) G B C - potential (2 * (q : ℤ) - 2) G C K := by
  rw [h.theta_eq, row_sum, deficiency_eq]
  unfold potential
  ring

lemma proper (h : Optimizer q G A B K C) (hi : Input q j G A B)
    (hK : K ⊆ B) (hp : 0 < thetaJ q j G A B K) : #C < #A := by
  have hne : C ≠ A := by
    intro heq
    have hc := card_sdiff_add_card_eq_card hK
    have he := ec_sdiff_add_right (G := G) hK A
    have hm := Bq.ec_lower_of_min (G := G) (sdiff_subset : B \ K ⊆ B) hi.minB
    rw [ec_comm] at hm
    have ht := h.theta_eq (j := j)
    rw [heq, row_sum] at ht
    have hcard := hi.card
    zify at hc he hm hcard
    nlinarith
  exact card_lt_card ⟨h.subset, fun hh => hne (Subset.antisymm h.subset hh)⟩

/-- H2/O1 with all zero optimizer rows allowed. -/
lemma positive_shape (h : Optimizer q G A B K C) (hi : Input q j G A B)
    (hK : K ⊆ B) (hlarge : q - 1 ≤ #K) (hp : 0 < thetaJ q j G A B K) :
    let k : ℤ := (#C : ℤ) - #K
    let ε := coreDefect q G C K - (3 * q - 31)
    1 - (j : ℤ) ≤ k ∧ k ≤ 2 ∧ 0 ≤ ε ∧
      ε + deficiency (2 * (q : ℤ) - 2) G B (A \ C) =
        j + k - thetaJ q j G A B K - 1 := by
  dsimp only
  let k : ℤ := (#C : ℤ) - #K
  have hq := hi.q_large
  have hj : (j : ℤ) ≤ 2 := by rcases hi.branch with hj | hj <;> omega
  have hclt := h.proper hi hK hp
  have hkle : #K ≤ #B := card_le_card hK
  have hal := hi.scar_le h.subset
  have han := hi.scar_nonneg h.subset
  have hbound : thetaJ q j G A B K ≤ (q : ℤ) * ((j : ℤ) + k) := by
    rw [h.theta_eq]
    have hs : (∑ a ∈ C, row q G B K a) ≤ (q : ℤ) * #C := by
      calc
        _ ≤ ∑ _a ∈ C, (q : ℤ) := by
          apply sum_le_sum
          intro a _
          have hd := dg_mono (G := G) hK a
          unfold row
          omega
        _ = _ := by simp [mul_comm]
    dsimp [k]
    nlinarith
  have hk0 : 1 - (j : ℤ) ≤ k := by
    by_contra! hbad
    have hh := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg q) (show (j : ℤ) + k ≤ 0 by omega)
    linarith
  have hsp := hi.sparse C h.subset K hK (by omega) (by omega)
  have ht := h.theta_potential (j := j)
  have he := hi.edge_cap_T h.subset hK
  have hg : (2 * (q : ℤ) - 2) * k ≤ potential (2 * (q : ℤ) - 2) G C K := by
    dsimp [k]
    unfold potential
    nlinarith
  have hk2 : k ≤ 2 := by
    by_contra! hbad
    have hprod : 0 ≤ ((q : ℤ) - 2) * (k - 3) := mul_nonneg (by omega) (by omega)
    dsimp [k] at hprod
    nlinarith
  have hε : 0 ≤ coreDefect q G C K - (3 * q - 31) := by
    have hh := twice_coreDefect (G := G) q C K
    omega
  have hsplit := hi.scar_split h.subset
  have hid : coreDefect q G C K - (3 * q - 31) + deficiency (2 * (q : ℤ) - 2) G B (A \ C) =
      j + k - thetaJ q j G A B K - 1 := by
    have hh := twice_coreDefect (G := G) q C K
    dsimp [k]
    nlinarith
  exact ⟨hk0, hk2, hε, hid⟩

lemma outward_edges (h : Optimizer q G A B K C) (hK : K ⊆ B) :
    (ec G C (B \ K) : ℤ) = (q : ℤ) * (j + ((#C : ℤ) - #K)) - thetaJ q j G A B K := by
  have he := ec_sdiff_add_right (G := G) hK C
  have ht := h.theta_eq (j := j)
  rw [row_sum] at ht
  zify at he
  nlinarith

lemma cross_scar_identity (h : Optimizer q G A B K C) :
    thetaJ q j G A B K = (q : ℤ) * j - ((q : ℤ) - 2) * ((#C : ℤ) - #K) +
      deficiency (2 * (q : ℤ) - 2) G B C - deficiency (2 * (q : ℤ) - 2) G A K -
      (ec G (A \ C) K : ℤ) := by
  have he := ec_sdiff_add_left (G := G) h.subset K
  rw [h.theta_eq, row_sum, deficiency_eq, deficiency_eq, ec_comm (G := G) K A]
  zify at he
  nlinarith

end Optimizer

/-- All original residual subsets are evaluated; no profile is supplied. -/
def extensionCost (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K P : Finset V) : ℤ := thetaJ q j G A B K - thetaJ q j G A B (K ∪ P)

def residualRows (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K C P : Finset V) : Finset V :=
  (A \ C).filter fun a => 0 < row q G B (K ∪ P) a

lemma extensionCost_empty (q j : ℕ) (A B K : Finset V) : extensionCost q j G A B K ∅ = 0 := by
  simp [extensionCost]

lemma extensionCost_submod (q j : ℕ) (A B K P Q : Finset V) :
    extensionCost q j G A B K (P ∪ Q) + extensionCost q j G A B K (P ∩ Q) ≤
      extensionCost q j G A B K P + extensionCost q j G A B K Q := by
  have hs := Input.theta_supermod (G := G) q j A B (K ∪ P) (K ∪ Q)
  rw [← union_union_distrib_left, ← union_inter_distrib_left] at hs
  unfold extensionCost
  linarith

lemma extensionCost_full {q j : ℕ} {A B K : Finset V} (hi : Input q j G A B) (hK : K ⊆ B) :
    extensionCost q j G A B K (B \ K) = thetaJ q j G A B K := by
  rw [extensionCost, union_sdiff_of_subset hK, hi.theta_full, sub_zero]

/-- H4/R1 exact original-unit residual cost, for every actual residual subset. -/
lemma extensionCost_units {q j : ℕ} {A B K C P : Finset V}
    (h : Optimizer q G A B K C) (hP : P ⊆ B \ K) :
    extensionCost q j G A B K P = (q : ℤ) * #P - ec G C P -
      ∑ a ∈ A \ C, max 0 (row q G B K a + dg G P a) := by
  have hdis : Disjoint K P := disjoint_left.mpr fun a haK haP => (mem_sdiff.mp (hP haP)).2 haK
  have hcard := card_union_of_disjoint hdis
  have hrow : ∀ a, row q G B (K ∪ P) a = row q G B K a + dg G P a := by
    intro a
    have hd := dg_union_of_disjoint (G := G) hdis a
    unfold row
    zify at hd
    omega
  have hinside : (∑ a ∈ C, max 0 (row q G B (K ∪ P) a)) =
      (∑ a ∈ C, row q G B K a) + ec G C P := by
    rw [ec, Nat.cast_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro a ha
    rw [hrow]
    exact max_eq_right (add_nonneg (h.inside a ha) (Nat.cast_nonneg _))
  have hs := sum_sdiff h.subset (f := fun a => max 0 (row q G B (K ∪ P) a))
  rw [hinside] at hs
  have htheta := h.theta_eq (j := j)
  unfold extensionCost thetaJ theta
  simp_rw [hrow] at hs
  simp_rw [hrow]
  zify at hcard
  unfold thetaJ theta at htheta
  nlinarith

lemma expanded_optimizer {q : ℕ} {A B K C P : Finset V}
    (h : Optimizer q G A B K C) (_hP : P ⊆ B \ K) :
    Optimizer q G A B (K ∪ P) (C ∪ residualRows q G A B K C P) := by
  have hJ : residualRows q G A B K C P ⊆ A \ C := filter_subset _ _
  have hmono : ∀ a, row q G B K a ≤ row q G B (K ∪ P) a := by
    intro a
    have hd := dg_mono (G := G) (subset_union_left : K ⊆ K ∪ P) a
    unfold row
    omega
  refine ⟨union_subset h.subset (hJ.trans sdiff_subset), ?_, ?_⟩
  · intro a ha
    rcases mem_union.mp ha with ha | ha
    · exact (h.inside a ha).trans (hmono a)
    · exact le_of_lt (mem_filter.mp ha).2
  · intro a ha
    have haA := (mem_sdiff.mp ha).1
    have haC : a ∉ C := fun hac => (mem_sdiff.mp ha).2 (mem_union_left _ hac)
    have haJ : a ∉ residualRows q G A B K C P := fun haj => (mem_sdiff.mp ha).2 (mem_union_right _ haj)
    by_contra! hp
    exact haJ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨haA, haC⟩, hp⟩)

/-- H4/R3 exact incidence identity, including the outside original scar. -/
lemma petal_resource_identity {q j : ℕ} {A B K C P : Finset V}
    (h : Optimizer q G A B K C) (hP : P ⊆ B \ K) :
    let J := residualRows q G A B K C P
    coreDefect q G J P = (ec G C P : ℤ) + ec G J K +
      deficiency (2 * (q : ℤ) - 2) G B J + extensionCost q j G A B K P - ((#P : ℤ) - #J) := by
  dsimp only
  let J := residualRows q G A B K C P
  have hdis : Disjoint K P := disjoint_left.mpr fun a haK haP => (mem_sdiff.mp (hP haP)).2 haK
  have hs : (∑ a ∈ A \ C, max 0 (row q G B K a + dg G P a)) =
      ∑ a ∈ J, (row q G B K a + dg G P a) := by
    have hr : ∀ a, row q G B (K ∪ P) a = row q G B K a + dg G P a := by
      intro a
      have hd := dg_union_of_disjoint (G := G) hdis a
      unfold row
      zify at hd
      omega
    dsimp [J, residualRows]
    rw [sum_filter]
    apply sum_congr rfl
    intro a _
    rw [hr]
    split_ifs with hp
    · exact max_eq_right (le_of_lt hp)
    · exact max_eq_left (le_of_not_gt hp)
  have hu := extensionCost_units (j := j) h hP
  rw [hs, sum_add_distrib, row_sum] at hu
  have hd : (∑ a ∈ J, (dg G P a : ℤ)) = ec G J P := by simp [ec, Nat.cast_sum]
  rw [hd] at hu
  rw [coreDefect, deficiency_eq]
  nlinarith

/-- Actual inclusion-maximal residual sets at a fixed cost. -/
def MaxPetal (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K : Finset V) (ell : ℤ) (P : Finset V) : Prop :=
  P ⊆ B \ K ∧ P.Nonempty ∧ extensionCost q j G A B K P = ell ∧
    ∀ Q ⊆ B \ K, P ⊆ Q → P ≠ Q → ell + 1 ≤ extensionCost q j G A B K Q

lemma MaxPetal.not_subset {q j : ℕ} {A B K P Q : Finset V} {ell : ℤ}
    (hP : MaxPetal q j G A B K ell P) (hQ : MaxPetal q j G A B K ell Q)
    (hne : P ≠ Q) : ¬P ⊆ Q := by
  intro hPQ
  have hh := hP.2.2.2 Q hQ.1 hPQ hne
  rw [hQ.2.2.1] at hh
  omega

/-- H4/R2 disjointness uses the minimum on ALL nonempty actual residual sets. -/
lemma MaxPetal.disjoint {q j : ℕ} {A B K P Q : Finset V} {ell : ℤ}
    (hmin : ∀ Z ⊆ B \ K, Z.Nonempty → ell ≤ extensionCost q j G A B K Z)
    (hP : MaxPetal q j G A B K ell P) (hQ : MaxPetal q j G A B K ell Q)
    (hne : P ≠ Q) : Disjoint P Q := by
  apply Finset.disjoint_left.mpr
  intro a haP haQ
  have hneU : P ≠ P ∪ Q := by
    intro he
    exact hQ.not_subset hP hne.symm (by simpa only [← he] using (subset_union_right : Q ⊆ P ∪ Q))
  have hcostU := hP.2.2.2 (P ∪ Q) (union_subset hP.1 hQ.1) subset_union_left hneU
  have hcostI := hmin (P ∩ Q) (inter_subset_left.trans hP.1) ⟨a, mem_inter.mpr ⟨haP, haQ⟩⟩
  have hs := extensionCost_submod (G := G) q j A B K P Q
  rw [hP.2.2.1, hQ.2.2.1] at hs
  omega

/-- H4/R2 the actual strict outside-row sets use the SAME gap resource. -/
lemma MaxPetal.rows_disjoint {q j : ℕ} {A B K C P Q : Finset V} {ell : ℤ}
    (hmin : ∀ Z ⊆ B \ K, Z.Nonempty → ell ≤ extensionCost q j G A B K Z)
    (hthreshold : ∀ a ∈ A \ C, ell ≤ -row q G B K a)
    (hP : MaxPetal q j G A B K ell P) (hQ : MaxPetal q j G A B K ell Q)
    (hne : P ≠ Q) : Disjoint (residualRows q G A B K C P) (residualRows q G A B K C Q) := by
  have hdis := hP.disjoint hmin hQ hne
  apply Finset.disjoint_left.mpr
  intro a haP haQ
  have haL := (mem_filter.mp haP).1
  have haA := (mem_sdiff.mp haL).1
  have hpa := (mem_filter.mp haP).2
  have hqa := (mem_filter.mp haQ).2
  have hca : a ∈ canonical q G A B (K ∪ P) ∩ canonical q G A B (K ∪ Q) :=
    mem_inter.mpr ⟨mem_filter.mpr ⟨haA, hpa⟩, mem_filter.mpr ⟨haA, hqa⟩⟩
  have hinter : (K ∪ P) ∩ (K ∪ Q) = K := by
    rw [← union_inter_distrib_left, disjoint_iff_inter_eq_empty.mp hdis, union_empty]
  have hu : (K ∪ P) ∪ (K ∪ Q) = K ∪ (P ∪ Q) := by
    ext v
    simp only [mem_union]
    tauto
  have hshared := bonus_shared (G := G) q hca
  rw [hinter] at hshared
  have hle : ell ≤ bonus q G B (K ∪ P) (K ∪ Q) a := by
    have hh := hthreshold a haL
    rw [hshared]
    unfold row at hh
    omega
  have hsum : bonus q G B (K ∪ P) (K ∪ Q) a ≤
      ∑ b ∈ A, bonus q G B (K ∪ P) (K ∪ Q) b :=
    single_le_sum (fun b _ => bonus_nonneg q B (K ∪ P) (K ∪ Q) b) haA
  have hid := bonus_sum (G := G) q A B (K ∪ P) (K ∪ Q)
  rw [hu, hinter] at hid
  have hneU : P ≠ P ∪ Q := by
    intro he
    exact hQ.not_subset hP hne.symm (by simpa only [← he] using (subset_union_right : Q ⊆ P ∪ Q))
  have hcU := hP.2.2.2 (P ∪ Q) (union_subset hP.1 hQ.1) subset_union_left hneU
  have hcP := hP.2.2.1
  have hcQ := hQ.2.2.1
  unfold extensionCost thetaJ at hcU hcP hcQ
  linarith

lemma exists_max_petal_extension {q j : ℕ} {A B K P : Finset V} {ell : ℤ}
    (hmin : ∀ Z ⊆ B \ K, Z.Nonempty → ell ≤ extensionCost q j G A B K Z)
    (hP : P ⊆ B \ K) (hne : P.Nonempty) (hcost : extensionCost q j G A B K P = ell) :
    ∃ Q, P ⊆ Q ∧ MaxPetal q j G A B K ell Q := by
  let F := (B \ K).powerset.filter fun Q => P ⊆ Q ∧ extensionCost q j G A B K Q = ell
  have hF : F.Nonempty := ⟨P, mem_filter.mpr ⟨mem_powerset.mpr hP, Subset.rfl, hcost⟩⟩
  obtain ⟨Q, hQ, hmax⟩ := exists_max_image F Finset.card hF
  obtain ⟨hqsub, hpq, hqc⟩ := mem_filter.mp hQ
  have hQsub := mem_powerset.mp hqsub
  refine ⟨Q, hpq, hQsub, hne.mono hpq, hqc, ?_⟩
  intro Z hZ hQZ hneQZ
  have hZne := hne.mono (hpq.trans hQZ)
  have hzmin := hmin Z hZ hZne
  by_contra! hbad
  have hzc : extensionCost q j G A B K Z = ell := by omega
  have hzF : Z ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hZ, hpq.trans hQZ, hzc⟩
  have hle := hmax Z hzF
  have hlt : #Q < #Z := card_lt_card ⟨hQZ, fun hZQ => hneQZ (Subset.antisymm hQZ hZQ)⟩
  omega

lemma residual_row_add (q : ℕ) {B K P : Finset V} (hP : P ⊆ B \ K) (a : V) :
    row q G B (K ∪ P) a = row q G B K a + dg G P a := by
  have hdis : Disjoint K P := Finset.disjoint_left.mpr fun _ haK haP => (mem_sdiff.mp (hP haP)).2 haK
  have hd := dg_union_of_disjoint (G := G) hdis a
  unfold row
  zify at hd
  omega

lemma extensionCost_le_linear {q j : ℕ} {A B K C P : Finset V}
    (h : Optimizer q G A B K C) (hP : P ⊆ B \ K) :
    extensionCost q j G A B K P ≤ (q : ℤ) * #P - ec G C P := by
  have hh := extensionCost_units (j := j) h hP
  have hn : 0 ≤ ∑ a ∈ A \ C, max 0 (row q G B K a + dg G P a) :=
    sum_nonneg fun _ _ => le_max_left _ _
  omega

lemma extensionCost_linear_of_no_rows {q j : ℕ} {A B K C P : Finset V}
    (h : Optimizer q G A B K C) (hP : P ⊆ B \ K)
    (hJ : residualRows q G A B K C P = ∅) :
    extensionCost q j G A B K P = (q : ℤ) * #P - ec G C P := by
  rw [extensionCost_units h hP]
  have hz : (∑ a ∈ A \ C, max 0 (row q G B K a + dg G P a)) = 0 := by
    apply sum_eq_zero
    intro a ha
    have hr : row q G B (K ∪ P) a ≤ 0 := by
      by_contra! hp
      have hm : a ∈ residualRows q G A B K C P := mem_filter.mpr ⟨ha, hp⟩
      rw [hJ] at hm
      simp at hm
    rw [residual_row_add q hP a] at hr
    exact max_eq_left hr
  rw [hz, sub_zero]

/-- A tiny petal is a physical singleton; it gets no ineligible floor. -/
lemma MaxPetal.tiny {q j : ℕ} {A B K C P : Finset V} {ell : ℤ}
    (h : Optimizer q G A B K C) (hell : 0 < ell)
    (hmin : ∀ Z ⊆ B \ K, Z.Nonempty → ell ≤ extensionCost q j G A B K Z)
    (hP : MaxPetal q j G A B K ell P) (hJ : residualRows q G A B K C P = ∅) :
    #P = 1 ∧ (ec G C P : ℤ) = q - ell := by
  have hc := extensionCost_linear_of_no_rows (j := j) h hP.1 hJ
  have hlo : ell * #P ≤ (q : ℤ) * #P - ec G C P := by
    have hs : (∑ b ∈ P, ((q : ℤ) - dg G C b)) = (q : ℤ) * #P - ec G C P := by
      rw [ec_comm (G := G) C P, ec, Nat.cast_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
      ring
    calc
      _ = ∑ _b ∈ P, ell := by simp only [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ b ∈ P, ((q : ℤ) - dg G C b) := by
        apply sum_le_sum
        intro b hb
        have hbsub : {b} ⊆ B \ K := singleton_subset_iff.mpr (hP.1 hb)
        have hm := hmin {b} hbsub (singleton_nonempty b)
        have hl := extensionCost_le_linear (j := j) h hbsub
        have he : ec G C {b} = dg G C b := by rw [ec_comm]; simp [ec]
        simp only [card_singleton, Nat.cast_one, mul_one, he] at hl
        omega
      _ = _ := hs
  have hne : 1 ≤ #P := card_pos.mpr hP.2.1
  have hcount : #P = 1 := by
    have hp := mul_nonneg (show 0 ≤ ell - 1 by omega) (show 0 ≤ (#P : ℤ) - 1 by omega)
    rw [hP.2.2.1] at hc
    nlinarith
  refine ⟨hcount, ?_⟩
  rw [hP.2.2.1, hcount] at hc
  norm_num at hc
  omega

/-- H4/R3 the expanded optimizer has a genuinely proper outside-row shore. -/
lemma MaxPetal.expanded_shape {q j : ℕ} {A B K C P : Finset V} {ell : ℤ}
    (hi : Input q j G A B) (h : Optimizer q G A B K C)
    (hK : K ⊆ B) (hlarge : q - 1 ≤ #K) (hheight : thetaJ q j G A B K = ell + 1)
    (hP : MaxPetal q j G A B K ell P) :
    let J := residualRows q G A B K C P
    let k : ℤ := (#C : ℤ) - #K
    let t : ℤ := (#P : ℤ) - #J
    #J < #(A \ C) ∧ k - 2 ≤ t ∧ t ≤ k + j - 2 := by
  dsimp only
  let J := residualRows q G A B K C P
  have hJ : J ⊆ A \ C := filter_subset _ _
  have hCJ : Disjoint C J := Finset.disjoint_left.mpr fun _ haC haJ => (mem_sdiff.mp (hJ haJ)).2 haC
  have hKP : Disjoint K P := Finset.disjoint_left.mpr fun _ haK haP => (mem_sdiff.mp (hP.1 haP)).2 haK
  have hopt := expanded_optimizer h hP.1
  change Optimizer q G A B (K ∪ P) (C ∪ J) at hopt
  have hext : thetaJ q j G A B (K ∪ P) = 1 := by
    have hc := hP.2.2.1
    unfold extensionCost at hc
    omega
  have hsub : K ∪ P ⊆ B := union_subset hK (hP.1.trans sdiff_subset)
  have hla : q - 1 ≤ #(K ∪ P) := hlarge.trans (card_le_card subset_union_left)
  have hprop := hopt.proper hi hsub (by omega)
  have hshape := hopt.positive_shape hi hsub hla (by omega)
  dsimp only at hshape
  have hscar := hi.scar_nonneg (sdiff_subset : A \ (C ∪ J) ⊆ A)
  have hcJ := card_union_of_disjoint hCJ
  have hcP := card_union_of_disjoint hKP
  have hcL := card_sdiff_add_card_eq_card h.subset
  change #(C ∪ J) < #A at hprop
  change 1 - (j : ℤ) ≤ (#(C ∪ J) : ℤ) - #(K ∪ P) ∧
    (#(C ∪ J) : ℤ) - #(K ∪ P) ≤ 2 ∧ _ at hshape
  zify at hcJ hcP hcL
  change #J < #(A \ C) ∧ ((#C : ℤ) - #K) - 2 ≤ (#P : ℤ) - #J ∧
    (#P : ℤ) - #J ≤ ((#C : ℤ) - #K) + j - 2
  omega

/-- H4/R3 a nonempty strict row set pays the eligible original proper floor. -/
lemma MaxPetal.large_resource {q j : ℕ} {A B K C P : Finset V} {ell : ℤ}
    (hi : Input q j G A B) (h : Optimizer q G A B K C)
    (hK : K ⊆ B) (hlarge : q - 1 ≤ #K) (hheight : thetaJ q j G A B K = ell + 1)
    (hell : 0 < ell) (hthreshold : ∀ a ∈ A \ C, ell ≤ -row q G B K a)
    (hP : MaxPetal q j G A B K ell P) (hneJ : (residualRows q G A B K C P).Nonempty) :
    let J := residualRows q G A B K C P
    3 * (q : ℤ) - 31 - ell + ((#P : ℤ) - #J) ≤
      (ec G C P : ℤ) + ec G J K + deficiency (2 * (q : ℤ) - 2) G B J := by
  dsimp only
  let J := residualRows q G A B K C P
  have hJ : J ⊆ A \ C := filter_subset _ _
  have hshape := hP.expanded_shape hi h hK hlarge hheight
  dsimp only at hshape
  have hJcount : #J < #(A \ C) := hshape.1
  obtain ⟨a, ha⟩ := hneJ
  have hpos := (mem_filter.mp ha).2
  have hth := hthreshold a ((mem_filter.mp ha).1)
  rw [residual_row_add q hP.1 a] at hpos
  have hd := dg_le_card (G := G) P a
  have hPl : 2 ≤ #P := by omega
  have hJl : 1 ≤ #J := card_pos.mpr ⟨a, ha⟩
  have hJltA : #J < #A := by
    have hLe := card_le_card (sdiff_subset : A \ C ⊆ A)
    omega
  have hPcard := card_le_card (hP.1.trans sdiff_subset)
  have hsp := hi.sparse J (hJ.trans sdiff_subset) P (hP.1.trans sdiff_subset) (by omega) (by omega)
  have ht := twice_coreDefect (G := G) q J P
  have hid := petal_resource_identity (j := j) h hP.1
  dsimp only at hid
  rw [hP.2.2.1] at hid
  change coreDefect q G J P = _ at hid
  omega

def petalWeight (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K C P : Finset V) : ℤ :=
  let J := residualRows q G A B K C P
  (ec G C P : ℤ) + ec G J K + deficiency (2 * (q : ℤ) - 2) G B J

lemma petalWeight_nonneg {q j : ℕ} {A B K C P : Finset V} (hi : Input q j G A B) :
    0 ≤ petalWeight q G A B K C P := by
  have hs := hi.scar_nonneg (show residualRows q G A B K C P ⊆ A from
    (filter_subset _ _).trans sdiff_subset)
  dsimp only [petalWeight]
  omega

/-- H4/R3 one simultaneous pool for the whole actual disjoint family. -/
lemma original_petal_pool {q j : ℕ} {A B K C : Finset V} (hi : Input q j G A B)
    (F : Finset (Finset V)) (hF : ∀ P ∈ F, P ⊆ B \ K)
    (hPdis : (F : Set (Finset V)).PairwiseDisjoint id)
    (hJdis : (F : Set (Finset V)).PairwiseDisjoint (residualRows q G A B K C)) :
    (∑ P ∈ F, petalWeight q G A B K C P) ≤ (ec G C (B \ K) : ℤ) +
      ec G (A \ C) K + deficiency (2 * (q : ℤ) - 2) G B (A \ C) := by
  let JP := residualRows q G A B K C
  have hsubP : F.biUnion id ⊆ B \ K := by
    intro v hv
    obtain ⟨P, hPF, hvP⟩ := mem_biUnion.mp hv
    exact hF P hPF hvP
  have hsubJ : F.biUnion JP ⊆ A \ C := by
    intro a ha
    obtain ⟨P, _, haJ⟩ := mem_biUnion.mp ha
    exact (mem_filter.mp haJ).1
  have hsP : (∑ P ∈ F, (ec G C P : ℤ)) = ec G C (F.biUnion id) := by
    simp_rw [ec_comm (G := G) C, ec, Nat.cast_sum]
    exact (sum_biUnion hPdis).symm
  have hsJ : (∑ P ∈ F, ((ec G (JP P) K : ℤ) + deficiency (2 * (q : ℤ) - 2) G B (JP P))) =
      ∑ a ∈ F.biUnion JP, ((dg G K a : ℤ) + (2 * (q : ℤ) - 2 - dg G B a)) := by
    simp_rw [ec, Nat.cast_sum, deficiency, ← sum_add_distrib]
    exact (sum_biUnion hJdis).symm
  have hlP : (ec G C (F.biUnion id) : ℤ) ≤ ec G C (B \ K) := by
    exact_mod_cast ec_mono_right (G := G) C hsubP
  have hlJ : (∑ a ∈ F.biUnion JP, ((dg G K a : ℤ) + (2 * (q : ℤ) - 2 - dg G B a))) ≤
      ec G (A \ C) K + deficiency (2 * (q : ℤ) - 2) G B (A \ C) := by
    have hh := sum_le_sum_of_subset_of_nonneg
      (f := fun a => ((dg G K a : ℤ) + (2 * (q : ℤ) - 2 - dg G B a))) hsubJ (fun a ha _ => by
      have hc := hi.capA_int (mem_sdiff.mp ha).1
      have hd : (0 : ℤ) ≤ dg G K a := Nat.cast_nonneg _
      omega)
    calc
      _ ≤ ∑ a ∈ A \ C, ((dg G K a : ℤ) + (2 * (q : ℤ) - 2 - dg G B a)) := hh
      _ = _ := by rw [sum_add_distrib]; simp only [ec, Nat.cast_sum, deficiency]
  unfold petalWeight
  change (∑ P ∈ F, ((ec G C P : ℤ) + (ec G (JP P) K : ℤ) +
    deficiency (2 * (q : ℤ) - 2) G B (JP P))) ≤ _
  simp_rw [add_assoc]
  rw [sum_add_distrib, hsP, hsJ]
  linarith

/-- Complete-family finite counting. -/
lemma complete_family_uncovered (R ban : Finset V) (F : Finset (Finset V))
    (large : Finset V → Prop) [DecidablePred large] (weight : Finset V → ℤ)
    (W L H : ℤ) (u v t h b : ℕ)
    (_hF : ∀ P ∈ F, P ⊆ R) (_hban : ban ⊆ R) (hbanCard : #ban ≤ b)
    (hweight : ∀ P ∈ F, 0 ≤ weight P)
    (hlarge : ∀ P ∈ F, large P → L ≤ weight P ∧ #P ≤ u + v)
    (htiny : ∀ P ∈ F, ¬large P → #P = 1 ∧ weight P = W)
    (hsum : (∑ P ∈ F, weight P) ≤ H)
    (hW : 0 < W) (h2L : H < 2 * L)
    (hrest : H - L < W * (t + 1)) (hall : H < W * (h + 1))
    (hgap : u + v + t + b < #R) (hgapTiny : h + b < #R) :
    ∃ z ∈ R, z ∉ ban ∧ ∀ P ∈ F, z ∉ P := by
  have hunique : ∀ P ∈ F, large P → ∀ Q ∈ F, large Q → P = Q := by
    intro P hPF hPl Q hQF hQl
    by_contra hn
    have hsub : {P, Q} ⊆ F := by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hPF, hQF⟩
    have hpq := sum_le_sum_of_subset_of_nonneg hsub (fun S hSF _ => hweight S hSF)
    have hp := (hlarge P hPF hPl).1
    have hq := (hlarge Q hQF hQl).1
    simp only [sum_insert (notMem_singleton.mpr hn), sum_singleton] at hpq
    omega
  have hcoverCard : #(F.biUnion id ∪ ban) < #R := by
    have hunion : #(F.biUnion id ∪ ban) ≤ #(F.biUnion id) + #ban := card_union_le _ _
    have hbi : #(F.biUnion id) ≤ ∑ P ∈ F, #P := card_biUnion_le
    by_cases hex : ∃ P ∈ F, large P
    · obtain ⟨P, hPF, hPl⟩ := hex
      have hrestTiny : ∀ Q ∈ F.erase P, #Q = 1 ∧ weight Q = W := by
        intro Q hQ
        obtain ⟨hQP, hQF⟩ := mem_erase.mp hQ
        apply htiny Q hQF
        intro hQl
        exact hQP (hunique Q hQF hQl P hPF hPl)
      have hrestWeight : (∑ Q ∈ F.erase P, weight Q) = W * #(F.erase P) := by
        calc
          _ = ∑ _Q ∈ F.erase P, W := sum_congr rfl fun Q hQ => (hrestTiny Q hQ).2
          _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
      have hrestCard : (∑ Q ∈ F.erase P, #Q) = #(F.erase P) := by
        calc
          _ = ∑ _Q ∈ F.erase P, 1 := sum_congr rfl fun Q hQ => (hrestTiny Q hQ).1
          _ = _ := by simp
      have hweightSplit := sum_erase_add F weight hPF
      have hcardSplit := sum_erase_add F Finset.card hPF
      rw [hrestWeight] at hweightSplit
      rw [hrestCard] at hcardSplit
      have hlargeBounds := hlarge P hPF hPl
      have hcount : #(F.erase P) ≤ t := by
        by_contra! hbad
        have hp : 0 ≤ W * ((#(F.erase P) : ℤ) - t - 1) := mul_nonneg (by omega) (by omega)
        nlinarith
      omega
    · have hnone : ∀ P ∈ F, ¬large P := by simpa only [not_exists, not_and] using hex
      have hweights : (∑ P ∈ F, weight P) = W * #F := by
        calc
          _ = ∑ _P ∈ F, W := sum_congr rfl fun P hP => (htiny P hP (hnone P hP)).2
          _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
      have hcards : (∑ P ∈ F, #P) = #F := by
        calc
          _ = ∑ _P ∈ F, 1 := sum_congr rfl fun P hP => (htiny P hP (hnone P hP)).1
          _ = _ := by simp
      have hcount : #F ≤ h := by
        by_contra! hbad
        have hp : 0 ≤ W * ((#F : ℤ) - h - 1) := mul_nonneg (by omega) (by omega)
        nlinarith
      omega
  have hex : ∃ z ∈ R, z ∉ F.biUnion id ∪ ban := by
    by_contra! hn
    have hs : R ⊆ F.biUnion id ∪ ban := hn
    have hc := card_le_card hs
    omega
  obtain ⟨z, hzR, hz⟩ := hex
  refine ⟨z, hzR, fun hzb => hz (mem_union_right _ hzb), ?_⟩
  intro P hP hzP
  exact hz (mem_union_left _ (mem_biUnion.mpr ⟨P, hP, hzP⟩))

/-- H4 finite counting applied to ALL actual maximal petals, before case specialization. -/
lemma residual_uncovered {q j : ℕ} {A B K C ban : Finset V}
    (hi : Input q j G A B) (hopt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hlargeK : q - 1 ≤ #K) (ell H : ℤ) (k t h b : ℕ)
    (hell : 0 < ell) (hheight : thetaJ q j G A B K = ell + 1)
    (hkc : #C = #K + k) (hkj : 3 ≤ k + j)
    (hmin : ∀ Z ⊆ B \ K, Z.Nonempty → ell ≤ extensionCost q j G A B K Z)
    (hthreshold : ∀ a ∈ A \ C, ell ≤ -row q G B K a)
    (hpool : (ec G C (B \ K) : ℤ) + ec G (A \ C) K +
      deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤ H)
    (hban : ban ⊆ B \ K) (hbanCard : #ban ≤ b)
    (hW : 0 < (q : ℤ) - ell)
    (h2L : H < 2 * (3 * (q : ℤ) + k - ell - 33))
    (hrest : H - (3 * (q : ℤ) + k - ell - 33) < ((q : ℤ) - ell) * (t + 1))
    (hall : H < ((q : ℤ) - ell) * (h + 1))
    (hgap : #(A \ C) + (k + j - 3) + t + b < #(B \ K))
    (hgapTiny : h + b < #(B \ K)) :
    ∃ z ∈ B \ K, z ∉ ban ∧ ∀ P ⊆ B \ K, P.Nonempty →
      extensionCost q j G A B K P = ell → z ∉ P := by
  let F := (B \ K).powerset.filter fun P => MaxPetal q j G A B K ell P
  have hf : ∀ P ∈ F, MaxPetal q j G A B K ell P := fun _ hP => (mem_filter.mp hP).2
  have hFsub : ∀ P ∈ F, P ⊆ B \ K := fun P hP => (hf P hP).1
  have hdisP : (F : Set (Finset V)).PairwiseDisjoint id := by
    intro P hP Q hQ hPQ
    exact (hf P hP).disjoint hmin (hf Q hQ) hPQ
  have hdisJ : (F : Set (Finset V)).PairwiseDisjoint (residualRows q G A B K C) := by
    intro P hP Q hQ hPQ
    exact (hf P hP).rows_disjoint hmin hthreshold (hf Q hQ) hPQ
  have hsum : (∑ P ∈ F, petalWeight q G A B K C P) ≤ H :=
    (original_petal_pool hi F hFsub hdisP hdisJ).trans hpool
  have hlarge : ∀ P ∈ F, (residualRows q G A B K C P).Nonempty →
      3 * (q : ℤ) + k - ell - 33 ≤ petalWeight q G A B K C P ∧
        #P ≤ #(A \ C) + (k + j - 3) := by
    intro P hPF hJP
    have hP := hf P hPF
    have hs := hP.expanded_shape hi hopt hK hlargeK hheight
    have hw := hP.large_resource hi hopt hK hlargeK hheight hell hthreshold hJP
    dsimp only at hs hw
    have hweight : petalWeight q G A B K C P =
        (ec G C P : ℤ) + ec G (residualRows q G A B K C P) K +
          deficiency (2 * (q : ℤ) - 2) G B (residualRows q G A B K C P) := rfl
    have hJlt := hs.1
    have htlo := hs.2.1
    have hthi := hs.2.2
    zify at hkc
    constructor
    · rw [hweight]
      omega
    · omega
  have htiny : ∀ P ∈ F, ¬(residualRows q G A B K C P).Nonempty →
      #P = 1 ∧ petalWeight q G A B K C P = (q : ℤ) - ell := by
    intro P hPF hn
    have hJ : residualRows q G A B K C P = ∅ := not_nonempty_iff_eq_empty.mp hn
    have ht := (hf P hPF).tiny hopt hell hmin hJ
    refine ⟨ht.1, ?_⟩
    dsimp only [petalWeight]
    rw [hJ]
    simp only [ec, sum_empty, Nat.cast_zero, deficiency, add_zero]
    exact ht.2
  obtain ⟨z, hzR, hzban, hzF⟩ := complete_family_uncovered (B \ K) ban F
    (fun P => (residualRows q G A B K C P).Nonempty) (petalWeight q G A B K C)
    ((q : ℤ) - ell) (3 * (q : ℤ) + k - ell - 33) H #(A \ C) (k + j - 3) t h b
    hFsub hban hbanCard (fun _ _ => petalWeight_nonneg hi) hlarge htiny hsum
    hW h2L hrest hall hgap hgapTiny
  refine ⟨z, hzR, hzban, ?_⟩
  intro P hP hPne hPc hzP
  obtain ⟨Q, hPQ, hQ⟩ := exists_max_petal_extension hmin hP hPne hPc
  have hQF : Q ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hQ.1, hQ⟩
  exact hzF Q hQF (hPQ hzP)

lemma Input.row_scar_le_set {q j : ℕ} {A B X : Finset V} (hi : Input q j G A B)
    (hX : X ⊆ A) {a : V} (ha : a ∈ X) :
    2 * (q : ℤ) - 2 - dg G B a ≤ deficiency (2 * (q : ℤ) - 2) G B X := by
  have hh := deficiency_le_subset (G := G) (2 * (q : ℤ) - 2)
    (singleton_subset_iff.mpr ha) (fun b hb => hi.capA_int (hX hb))
  simpa [deficiency] using hh

omit [DecidableEq V] in
lemma dg_le_ec_left {X Y : Finset V} {a : V} (ha : a ∈ X) : dg G Y a ≤ ec G X Y := by
  exact single_le_sum (fun _ _ => Nat.zero_le _) ha

/-- Original resource identities shared by the high and local cores. -/
lemma Optimizer.resource_bounds {q j : ℕ} {A B K C : Finset V}
    (h : Optimizer q G A B K C) (hi : Input q j G A B) (hK : K ⊆ B) :
    (ec G (A \ C) K : ℤ) + deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤
      3 * (q : ℤ) - 32 + j - thetaJ q j G A B K -
        ((q : ℤ) - 2) * ((#C : ℤ) - #K) := by
  have ht := h.cross_scar_identity (j := j)
  have hs := hi.scar_split h.subset
  have hn : 0 ≤ deficiency (2 * (q : ℤ) - 2) G A K :=
    deficiency_nonneg _ fun b hb => hi.capB_int (hK hb)
  nlinarith

lemma Optimizer.residual_card {q j : ℕ} {A B K C : Finset V}
    (h : Optimizer q G A B K C) (hi : Input q j G A B) (hK : K ⊆ B) :
    (#(B \ K) : ℤ) = #(A \ C) + j + ((#C : ℤ) - #K) := by
  have ha := card_sdiff_add_card_eq_card h.subset
  have hb := card_sdiff_add_card_eq_card hK
  have hc := hi.card
  omega

lemma strict_extension_cost_min {q j : ℕ} {A B K : Finset V} {ell : ℤ}
    (hK : K ⊆ B)
    (hbound : ∀ N ⊆ B, K ⊆ N → K ≠ N →
      thetaJ q j G A B N ≤ thetaJ q j G A B K - ell) :
    ∀ P ⊆ B \ K, P.Nonempty → ell ≤ extensionCost q j G A B K P := by
  intro P hP hne
  have hneU : K ≠ K ∪ P := by
    intro he
    obtain ⟨z, hz⟩ := hne
    have hzK : z ∈ K := by rw [he]; exact mem_union_right _ hz
    exact (mem_sdiff.mp (hP hz)).2 hzK
  have hh := hbound (K ∪ P) (union_subset hK (hP.trans sdiff_subset)) subset_union_left hneU
  unfold extensionCost
  omega

lemma GreatestHigh.cost_min {q j : ℕ} {A B K : Finset V}
    (hK : GreatestHigh q j G A B K) :
    ∀ P ⊆ B \ K, P.Nonempty → 1 ≤ extensionCost q j G A B K P := by
  apply strict_extension_cost_min hK.positive.1
  intro N hN hKN hne
  by_contra! hbad
  have hp : LargePositive q j G A B N :=
    ⟨hN, hK.positive.2.1.trans (card_le_card hKN), by have hk := hK.positive.2.2; omega⟩
  have hl := hK.height N hp
  have he : thetaJ q j G A B N = thetaJ q j G A B K := by omega
  exact hne (Subset.antisymm hKN (hK.contains_high N hp he))

/-- H4 exact high-core resources, including the real availability of residual vertices. -/
lemma high_geometry {q j : ℕ} {A B K : Finset V} (hi : Input q j G A B)
    (hK : GreatestHigh q j G A B K) (hheight : thetaJ q j G A B K = j + 1) :
    let C := canonical q G A B K
    #C = #K + 2 ∧ deficiency (2 * (q : ℤ) - 2) G B (A \ C) = 0 ∧
      (ec G C (B \ K) : ℤ) = (q : ℤ) * (j + 2) - (j + 1) ∧
      (ec G (A \ C) K : ℤ) ≤ q - 29 ∧
      #(B \ K) = #(A \ C) + j + 2 ∧ q + 27 ≤ #(B \ K) ∧
      ∀ a ∈ A \ C, (dg G B a : ℤ) = 2 * q - 2 ∧ 27 ≤ -row q G B K a := by
  dsimp only
  let C := canonical q G A B K
  change #C = #K + 2 ∧ deficiency (2 * (q : ℤ) - 2) G B (A \ C) = 0 ∧
    (ec G C (B \ K) : ℤ) = (q : ℤ) * (j + 2) - (j + 1) ∧
    (ec G (A \ C) K : ℤ) ≤ q - 29 ∧ #(B \ K) = #(A \ C) + j + 2 ∧
    q + 27 ≤ #(B \ K) ∧ ∀ a ∈ A \ C, (dg G B a : ℤ) = 2 * q - 2 ∧ 27 ≤ -row q G B K a
  have ho := strict_optimizer (G := G) q A B K
  change Optimizer q G A B K C at ho
  have hs := ho.positive_shape hi hK.positive.1 hK.positive.2.1 hK.positive.2.2
  dsimp only at hs
  have hsc := hi.scar_nonneg (sdiff_subset : A \ C ⊆ A)
  have hk : (#C : ℤ) - #K = 2 := by change _ at hs; omega
  have hz : deficiency (2 * (q : ℤ) - 2) G B (A \ C) = 0 := by
    change _ at hs
    omega
  have hcount : #C = #K + 2 := by omega
  have he := ho.outward_edges (j := j) hK.positive.1
  have hiBound := ho.resource_bounds hi hK.positive.1
  rw [hk, hheight] at he
  rw [hk, hheight, hz] at hiBound
  have hI : (ec G (A \ C) K : ℤ) ≤ q - 29 := by nlinarith only [hiBound]
  have hrc := ho.residual_card hi hK.positive.1
  rw [hk] at hrc
  have hrows : ∀ a ∈ A \ C, (dg G B a : ℤ) = 2 * q - 2 ∧ 27 ≤ -row q G B K a := by
    intro a ha
    have hsa := hi.row_scar_le_set (sdiff_subset : A \ C ⊆ A) ha
    rw [hz] at hsa
    have hc := hi.capA_int (mem_sdiff.mp ha).1
    have hd := dg_le_ec_left (G := G) (Y := K) ha
    constructor
    · omega
    · unfold row
      omega
  have hRlarge : q + 27 ≤ #(B \ K) := by
    have hCL : #C < #A := ho.proper hi hK.positive.1 hK.positive.2.2
    have hLcard := card_sdiff_add_card_eq_card ho.subset
    have hLne : (A \ C).Nonempty := card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hLne
    have har := hrows a ha
    have hd := dg_sdiff_add (G := G) hK.positive.1 a
    have hec := dg_le_ec_left (G := G) (Y := K) ha
    have hr := dg_le_card (G := G) (B \ K) a
    omega
  change #C = #K + 2 ∧ deficiency (2 * (q : ℤ) - 2) G B (A \ C) = 0 ∧ _
  exact ⟨hcount, hz, he, hI, by omega, hRlarge, hrows⟩

/-- H5 local theta-two geometry uses the equality-inclusive original optimizer. -/
lemma local_two_geometry {q : ℕ} {A B K : Finset V} (hi : Input q 2 G A B)
    (hK : K ⊆ B) (hlarge : q - 1 ≤ #K) (hheight : thetaJ q 2 G A B K = 2) :
    let C := weakCore q G A B K
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ #C = #K + k ∧
      deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤ 1 ∧
      (ec G C (B \ K) : ℤ) + ec G (A \ C) K +
        deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤ 5 * q + 2 * k - 34 ∧
      #(B \ K) = #(A \ C) + k + 2 ∧ 27 ≤ #(B \ K) := by
  dsimp only
  let C := weakCore q G A B K
  change ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ #C = #K + k ∧
    deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤ 1 ∧
    (ec G C (B \ K) : ℤ) + ec G (A \ C) K + deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤ 5 * q + 2 * k - 34 ∧
    #(B \ K) = #(A \ C) + k + 2 ∧ 27 ≤ #(B \ K)
  have ho := weak_optimizer (G := G) q A B K
  change Optimizer q G A B K C at ho
  have hs := ho.positive_shape hi hK hlarge (by omega)
  dsimp only at hs
  have hsc := hi.scar_nonneg (sdiff_subset : A \ C ⊆ A)
  have hk : (#C : ℤ) - #K = 1 ∨ (#C : ℤ) - #K = 2 := by omega
  have hq := hi.q_large
  rcases hk with hk | hk
  all_goals
    have hz : deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤ 1 := by omega
    have he := ho.outward_edges (j := 2) hK
    have hiBound := ho.resource_bounds hi hK
    have hrc := ho.residual_card hi hK
    rw [hk, hheight] at he hiBound
    rw [hk] at hrc
    have hRlarge : 27 ≤ #(B \ K) := by
      have hCL : #C < #A := ho.proper hi hK (by omega)
      have hLcard := card_sdiff_add_card_eq_card ho.subset
      have hLne : (A \ C).Nonempty := card_pos.mp (by omega)
      obtain ⟨a, ha⟩ := hLne
      have hsa := hi.row_scar_le_set (sdiff_subset : A \ C ⊆ A) ha
      have hd := dg_sdiff_add (G := G) hK a
      have hec := dg_le_ec_left (G := G) (Y := K) ha
      have hr := dg_le_card (G := G) (B \ K) a
      omega
  · refine ⟨1, Or.inl rfl, by omega, hz, ?_, by omega, hRlarge⟩
    norm_num at he hiBound ⊢
    nlinarith only [he, hiBound]
  · refine ⟨2, Or.inr rfl, by omega, hz, ?_, by omega, hRlarge⟩
    norm_num at he hiBound ⊢
    nlinarith only [he, hiBound]

omit [DecidableEq V] in
lemma GreatestHigh.strict_height {q j : ℕ} {A B K : Finset V}
    (hK : GreatestHigh q j G A B K) :
    ∀ N ⊆ B, K ⊆ N → K ≠ N → thetaJ q j G A B N ≤ thetaJ q j G A B K - 1 := by
  intro N hN hKN hne
  by_contra! hbad
  have hp : LargePositive q j G A B N :=
    ⟨hN, hK.positive.2.1.trans (card_le_card hKN), by have hk := hK.positive.2.2; omega⟩
  have hl := hK.height N hp
  have he : thetaJ q j G A B N = thetaJ q j G A B K := by omega
  exact hne (Subset.antisymm hKN (hK.contains_high N hp he))

omit [DecidableEq V] in
lemma GreatestHigh.height_one_contains {q j : ℕ} {A B K T : Finset V}
    (hK : GreatestHigh q j G A B K) (hheight : thetaJ q j G A B K = 1)
    (hT : LargePositive q j G A B T) : T ⊆ K := by
  have hh := hK.height T hT
  have hp := hT.2.2
  exact hK.contains_high T hT (by omega)

omit [DecidableEq V] in
lemma Input.one_positive_classification {q : ℕ} {A B T : Finset V}
    (hi : Input q 1 G A B) (hne : T.Nonempty) (hp : 0 < thetaJ q 1 G A B T) :
    #T = 1 ∨ q - 1 ≤ #T := by
  have hc : 1 ≤ #T := card_pos.mpr hne
  by_cases hlarge : q - 1 ≤ #T
  · exact Or.inr hlarge
  · have hsmall : #T ≤ q - 2 := by omega
    by_cases ht : #T = 2
    · have hh := hi.theta_pair_one ht
      omega
    · by_cases hmid : 3 ≤ #T
      · have hh := hi.theta_intermediate hmid hsmall
        omega
      · exact Or.inl (by omega)

lemma Input.two_positive_large {q : ℕ} {A B T : Finset V}
    (hi : Input q 2 G A B) (ht : 2 ≤ #T) (hp : 0 < thetaJ q 2 G A B T) :
    q - 1 ≤ #T := by
  by_contra! hbad
  have hsmall : #T ≤ q - 2 := by omega
  by_cases hmid : 3 ≤ #T
  · have hh := hi.theta_intermediate hmid hsmall
    omega
  · have he : #T = 2 := by omega
    have hh := hi.theta_tiny_two (T := T) (by omega)
    rw [he] at hh
    norm_num at hh
    omega

omit [DecidableEq V] in
lemma Input.singleton_nonpositive {q : ℕ} {A B : Finset V}
    (hi : Input q 1 G A B) (b : V)
    (hgood : ∀ a ∈ A, dg G B a = q → ¬G.Adj a b) : thetaJ q 1 G A B {b} ≤ 0 := by
  have hz : ∀ a ∈ A, max 0 (row q G B {b} a) = 0 := by
    intro a ha
    have hm := hi.minA a ha
    have hd := dg_le_card (G := G) {b} a
    by_cases he : dg G B a = q
    · have hna := hgood a ha he
      have hzero : dg G {b} a = 0 := by simp [dg, hna]
      unfold row
      rw [he, hzero]
      simp
    · unfold row
      simp only [card_singleton] at hd
      omega
  simp only [thetaJ, theta, card_singleton, Nat.cast_one, mul_one, sum_eq_zero hz]
  omega

/-- H5 the complete original bad-singleton set and its common large-core bound. -/
lemma Input.bad_singleton_data {q : ℕ} {A B : Finset V} (hi : Input q 1 G A B) :
    ∃ N : Finset V, N ⊆ B ∧ #N ≤ q ∧
      (∀ b ∈ B, b ∉ N → thetaJ q 1 G A B {b} ≤ 0) ∧
      ∀ K, LargePositive q 1 G A B K →
        (#(N \ K) : ℤ) ≤ ((#(canonical q G A B K) : ℤ) - #K) + 1 - thetaJ q 1 G A B K := by
  have hq := hi.q_large
  by_cases hex : ∃ a ∈ A, dg G B a = q
  · obtain ⟨a0, ha0, hd0⟩ := hex
    have huni : ∀ a ∈ A, dg G B a = q → a = a0 := by
      intro a ha hd
      by_contra hne
      have hsub : {a, a0} ⊆ A := by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨ha, ha0⟩
      have hs := hi.scar_le hsub
      simp [deficiency, hne, hd, hd0] at hs
      omega
    let N := B.filter fun b => G.Adj a0 b
    have hN : N ⊆ B := filter_subset _ _
    have hNc : #N = q := hd0
    refine ⟨N, hN, by omega, ?_, ?_⟩
    · intro b hb hbN
      apply hi.singleton_nonpositive b
      intro a ha hd
      have he := huni a ha hd
      subst a
      intro hab
      exact hbN (mem_filter.mpr ⟨hb, hab⟩)
    · intro K hK
      have hs := hi.positive_shape hK.1 hK.2.1 hK.2.2
      dsimp only at hs
      have ho := hi.outside_scar_le hK.1 hK.2.1 hK.2.2
      have hac : a0 ∈ canonical q G A B K := by
        by_contra hn
        have hsrow := hi.row_scar_le_set (sdiff_subset : A \ canonical q G A B K ⊆ A)
          (mem_sdiff.mpr ⟨ha0, hn⟩)
        rw [hd0] at hsrow
        omega
      have hint := hi.canonical_internal_min hK.1 hK.2.1 hK.2.2 hac
      have hsc := hi.scar_nonneg (sdiff_subset : A \ canonical q G A B K ⊆ A)
      have hsplit := dg_sdiff_add (G := G) hK.1 a0
      have hcard : #(N \ K) = dg G (B \ K) a0 := by
        change #(N \ K) = #((B \ K).filter fun b => G.Adj a0 b)
        congr 1
        ext b
        simp only [N, mem_sdiff, mem_filter]
        tauto
      rw [hcard]
      rw [hd0] at hsplit
      omega
  · refine ⟨∅, empty_subset _, by simp, ?_, ?_⟩
    · intro b _ _
      apply hi.singleton_nonpositive b
      intro a ha hd
      exact False.elim (hex ⟨a, ha, hd⟩)
    · intro K hK
      have hs := hi.positive_shape hK.1 hK.2.1 hK.2.2
      dsimp only at hs
      have hsc := hi.scar_nonneg (sdiff_subset : A \ canonical q G A B K ⊆ A)
      simp only [empty_sdiff, card_empty, Nat.cast_zero]
      omega

omit [DecidableEq V] in
lemma one_good_cut {q : ℕ} {A B N : Finset V} (hi : Input q 1 G A B)
    (hsingle : ∀ b ∈ B, b ∉ N → thetaJ q 1 G A B {b} ≤ 0)
    {z : V} (hz : z ∈ B) (hzN : z ∉ N)
    (havoid : ∀ T, LargePositive q 1 G A B T → z ∉ T) :
    ∀ T ⊆ B, z ∈ T → thetaJ q 1 G A B T ≤ 0 := by
  intro T hT hzT
  by_contra! hp
  rcases hi.one_positive_classification ⟨z, hzT⟩ hp with hone | hlarge
  · obtain ⟨b, rfl⟩ := card_eq_one.mp hone
    have he : z = b := mem_singleton.mp hzT
    subst b
    have hh := hsingle z hz hzN
    omega
  · exact havoid T ⟨hT, hlarge, hp⟩ hzT

lemma two_good_cut {q : ℕ} {A B O : Finset V} (hi : Input q 2 G A B)
    (hO : #O = 2) (havoid : ∀ T, LargePositive q 2 G A B T → ¬O ⊆ T) :
    ∀ T ⊆ B, O ⊆ T → thetaJ q 2 G A B T ≤ 0 := by
  intro T hT hOT
  by_contra! hp
  have hc := card_le_card hOT
  have hl := hi.two_positive_large (by omega) hp
  exact havoid T ⟨hT, hl, hp⟩ hOT

lemma avoidance_from_residual {q j : ℕ} {A B K : Finset V} {ell : ℤ} {z : V}
    (_hK : K ⊆ B) (hheight : thetaJ q j G A B K = ell + 1)
    (hmin : ∀ P ⊆ B \ K, P.Nonempty → ell ≤ extensionCost q j G A B K P)
    (hz : z ∈ B \ K)
    (hgood : ∀ P ⊆ B \ K, P.Nonempty → extensionCost q j G A B K P = ell → z ∉ P) :
    ∀ N ⊆ B, K ⊆ N → 0 < thetaJ q j G A B N → z ∉ N := by
  intro N hN hKN hp hzN
  let P := N \ K
  have hP : P ⊆ B \ K := sdiff_subset_sdiff hN Subset.rfl
  have hzP : z ∈ P := mem_sdiff.mpr ⟨hzN, (mem_sdiff.mp hz).2⟩
  have hne : P.Nonempty := ⟨z, hzP⟩
  have he : K ∪ P = N := union_sdiff_of_subset hKN
  have hcost := hmin P hP hne
  have hc : extensionCost q j G A B K P = ell := by
    unfold extensionCost at hcost ⊢
    rw [he] at hcost ⊢
    omega
  exact hgood P hP hne hc hzP

lemma avoid_all_large_from_extensions {q j : ℕ} {A B K : Finset V} {z : V}
    (hi : Input q j G A B) (hK : GreatestHigh q j G A B K)
    (hgood : ∀ N ⊆ B, K ⊆ N → 0 < thetaJ q j G A B N → z ∉ N) :
    ∀ T, LargePositive q j G A B T → z ∉ T := by
  intro T hT hzT
  obtain ⟨M, hTM, hM⟩ := exists_max_large_extension q j hT
  have hKM := hK.subset_max hi hM
  exact hgood M hM.1.1 hKM hM.1.2.2 (hTM hzT)

/-- H5 local theta-two calculation, with every equality row absorbed. -/
lemma local_two_uncovered {q : ℕ} {A B K : Finset V} (hi : Input q 2 G A B)
    (hK : K ⊆ B) (hlarge : q - 1 ≤ #K) (hheight : thetaJ q 2 G A B K = 2)
    (hmax : ∀ N ⊆ B, K ⊆ N → K ≠ N → thetaJ q 2 G A B N ≤ 1) :
    ∃ z ∈ B \ K, ∀ N ⊆ B, K ⊆ N → 0 < thetaJ q 2 G A B N → z ∉ N := by
  let C := weakCore q G A B K
  have ho := weak_optimizer (G := G) q A B K
  change Optimizer q G A B K C at ho
  have hg := local_two_geometry hi hK hlarge hheight
  dsimp only at hg
  change ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ #C = #K + k ∧
    deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤ 1 ∧
    (ec G C (B \ K) : ℤ) + ec G (A \ C) K + deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤ 5 * q + 2 * k - 34 ∧
    #(B \ K) = #(A \ C) + k + 2 ∧ 27 ≤ #(B \ K) at hg
  obtain ⟨k, hk, hkc, _, hpool, hrc, hrl⟩ := hg
  have hq := hi.q_large
  have hmin : ∀ P ⊆ B \ K, P.Nonempty → 1 ≤ extensionCost q 2 G A B K P := by
    apply strict_extension_cost_min hK
    intro N hN hKN hne
    have hh := hmax N hN hKN hne
    omega
  have hthreshold : ∀ a ∈ A \ C, (1 : ℤ) ≤ -row q G B K a := by
    intro a ha
    have hh := weak_outside_strict (G := G) q A B K ha
    omega
  obtain ⟨z, hz, _, hzgood⟩ := residual_uncovered (ban := ∅) hi ho hK hlarge 1
    (5 * (q : ℤ) + 2 * k - 34) k 2 4 0 (by norm_num) (by omega) hkc (by rcases hk with hk | hk <;> omega)
    hmin hthreshold hpool (empty_subset _) (by simp)
    (by omega) (by nlinarith) (by rcases hk with hk | hk <;> subst k <;> norm_num <;> omega)
    (by rcases hk with hk | hk <;> subst k <;> norm_num <;> omega)
    (by omega) (by omega)
  exact ⟨z, hz, avoidance_from_residual hK (ell := 1) (by omega) hmin hz hzgood⟩

lemma MaxPetal.strict_theta {q j : ℕ} {A B K P : Finset V} {ell : ℤ}
    (_hK : K ⊆ B) (hP : MaxPetal q j G A B K ell P) :
    ∀ N ⊆ B, K ∪ P ⊆ N → K ∪ P ≠ N →
      thetaJ q j G A B N ≤ thetaJ q j G A B K - (ell + 1) := by
  intro N hN hKN hne
  let Q := N \ K
  have hQ : Q ⊆ B \ K := sdiff_subset_sdiff hN Subset.rfl
  have hKsub : K ⊆ N := subset_union_left.trans hKN
  have hPQ : P ⊆ Q := by
    intro a ha
    exact mem_sdiff.mpr ⟨hKN (mem_union_right _ ha), (mem_sdiff.mp (hP.1 ha)).2⟩
  have hnePQ : P ≠ Q := by
    intro he
    exact hne (by rw [he]; exact union_sdiff_of_subset hKsub)
  have hc := hP.2.2.2 Q hQ hPQ hnePQ
  unfold extensionCost at hc
  rw [union_sdiff_of_subset hKsub] at hc
  omega

/-- H5 surplus one: one original point pays every original theta cut. -/
theorem Input.common_omission_one {q : ℕ} {A B : Finset V} (hi : Input q 1 G A B) :
    ∃ z ∈ B, ∀ T ⊆ B, z ∈ T → thetaJ q 1 G A B T ≤ 0 := by
  obtain ⟨N, _hN, hNc, hsingle, hbad⟩ := hi.bad_singleton_data
  have hq := hi.q_large
  by_cases hex : ∃ T, LargePositive q 1 G A B T
  · obtain ⟨K, hK⟩ := exists_greatest_high hi hex
    have hp := hK.positive.2.2
    have hh := hi.theta_large_le hK.positive.1 hK.positive.2.1
    have hcases : thetaJ q 1 G A B K = 1 ∨ thetaJ q 1 G A B K = 2 := by omega
    rcases hcases with hheight | hheight
    · let C := canonical q G A B K
      have ho := strict_optimizer (G := G) q A B K
      change Optimizer q G A B K C at ho
      have hCprop := ho.proper hi hK.positive.1 hp
      have hLcard := card_sdiff_add_card_eq_card ho.subset
      have hRcard := ho.residual_card hi hK.positive.1
      have hb := hbad K hK.positive
      change (#(N \ K) : ℤ) ≤ ((#C : ℤ) - #K) + 1 - thetaJ q 1 G A B K at hb
      have hzex : ∃ z ∈ B \ K, z ∉ N := by
        by_contra! hn
        have hsub : B \ K ⊆ N \ K := by
          intro z hz
          exact mem_sdiff.mpr ⟨hn z hz, (mem_sdiff.mp hz).2⟩
        have hc := card_le_card hsub
        omega
      obtain ⟨z, hzR, hzN⟩ := hzex
      have havoid : ∀ T, LargePositive q 1 G A B T → z ∉ T := by
        intro T hT hzT
        have hTK := hK.height_one_contains hheight hT
        exact (mem_sdiff.mp hzR).2 (hTK hzT)
      exact ⟨z, (mem_sdiff.mp hzR).1, one_good_cut hi hsingle (mem_sdiff.mp hzR).1 hzN havoid⟩
    · let C := canonical q G A B K
      have ho := strict_optimizer (G := G) q A B K
      change Optimizer q G A B K C at ho
      have hg := high_geometry hi hK (by omega)
      dsimp only at hg
      have hkc : #C = #K + 2 := hg.1
      have hzero : deficiency (2 * (q : ℤ) - 2) G B (A \ C) = 0 := hg.2.1
      have hE : (ec G C (B \ K) : ℤ) = 3 * q - 2 := by
        have he : (ec G C (B \ K) : ℤ) = (q : ℤ) * (1 + 2) - (1 + 1) := hg.2.2.1
        norm_num at he
        nlinarith only [he]
      have hI : (ec G (A \ C) K : ℤ) ≤ q - 29 := hg.2.2.2.1
      have hRcard : #(B \ K) = #(A \ C) + 3 := by
        have hc : #(B \ K) = #(A \ C) + 1 + 2 := hg.2.2.2.2.1
        omega
      have hRlarge : q + 27 ≤ #(B \ K) := hg.2.2.2.2.2.1
      have hthreshold : ∀ a ∈ A \ C, (1 : ℤ) ≤ -row q G B K a := by
        intro a ha
        have hh := (hg.2.2.2.2.2.2 a ha).2
        omega
      have hmin := hK.cost_min
      have hpool : (ec G C (B \ K) : ℤ) + ec G (A \ C) K +
          deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤ 4 * q - 31 := by omega
      have hban : N \ K ⊆ B \ K := sdiff_subset_sdiff _hN Subset.rfl
      have hbanCard : #(N \ K) ≤ 1 := by
        have hb := hbad K hK.positive
        change (#(N \ K) : ℤ) ≤ ((#C : ℤ) - #K) + 1 - thetaJ q 1 G A B K at hb
        omega
      obtain ⟨z, hzR, hzban, hzgood⟩ := residual_uncovered hi ho hK.positive.1 hK.positive.2.1
        1 (4 * (q : ℤ) - 31) 2 1 3 1 (by norm_num) (by omega) hkc (by norm_num)
        hmin hthreshold hpool hban hbanCard (by omega) (by norm_num; omega)
        (by norm_num; omega) (by norm_num; omega) (by omega) (by omega)
      have hzN : z ∉ N := fun hzN => hzban (mem_sdiff.mpr ⟨hzN, (mem_sdiff.mp hzR).2⟩)
      have hext := avoidance_from_residual hK.positive.1 (ell := 1) (by omega) hmin hzR hzgood
      have havoid := avoid_all_large_from_extensions hi hK hext
      exact ⟨z, (mem_sdiff.mp hzR).1, one_good_cut hi hsingle (mem_sdiff.mp hzR).1 hzN havoid⟩
  · have hB := hi.shores_large.2
    have hzex : ∃ z ∈ B, z ∉ N := by
      by_contra! hn
      have hc := card_le_card (show B ⊆ N from hn)
      omega
    obtain ⟨z, hzB, hzN⟩ := hzex
    have havoid : ∀ T, LargePositive q 1 G A B T → z ∉ T := by
      intro T hT _
      exact hex ⟨T, hT⟩
    exact ⟨z, hzB, one_good_cut hi hsingle hzB hzN havoid⟩

lemma Input.omission_pair {q : ℕ} {A B : Finset V} (hi : Input q 2 G A B)
    {x z : V} (hx : x ∈ B) (hz : z ∈ B) (hne : x ≠ z)
    (havoid : ∀ T, LargePositive q 2 G A B T → x ∈ T → z ∉ T) :
    ∃ O : Finset V, O ⊆ B ∧ #O = 2 ∧ ∀ T ⊆ B, O ⊆ T → thetaJ q 2 G A B T ≤ 0 := by
  have hO : #{x, z} = 2 := by simp [hne]
  refine ⟨{x, z}, ?_, hO, two_good_cut hi hO ?_⟩
  · simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hx, hz⟩
  · intro T hT hOT
    exact havoid T hT (hOT (by simp)) (hOT (by simp))

/-- H5 high-three branch without cost-one residuals, over the entire original powerset. -/
lemma high_three_without_one {q : ℕ} {A B K : Finset V} (hi : Input q 2 G A B)
    (hK : GreatestHigh q 2 G A B K) (hheight : thetaJ q 2 G A B K = 3)
    (hnone : ¬∃ P ⊆ B \ K, P.Nonempty ∧ extensionCost q 2 G A B K P = 1) :
    ∃ z ∈ B \ K, ∀ N ⊆ B, K ⊆ N → 0 < thetaJ q 2 G A B N → z ∉ N := by
  let C := canonical q G A B K
  have ho := strict_optimizer (G := G) q A B K
  change Optimizer q G A B K C at ho
  have hg := high_geometry hi hK (by omega)
  dsimp only at hg
  have hq := hi.q_large
  have hkc : #C = #K + 2 := hg.1
  have hzero : deficiency (2 * (q : ℤ) - 2) G B (A \ C) = 0 := hg.2.1
  have hE : (ec G C (B \ K) : ℤ) = 4 * q - 3 := by
    have he : (ec G C (B \ K) : ℤ) = (q : ℤ) * (2 + 2) - (2 + 1) := hg.2.2.1
    norm_num at he
    nlinarith only [he]
  have hI : (ec G (A \ C) K : ℤ) ≤ q - 29 := hg.2.2.2.1
  have hRcard : #(B \ K) = #(A \ C) + 4 := by
    have hc : #(B \ K) = #(A \ C) + 2 + 2 := hg.2.2.2.2.1
    omega
  have hRlarge : q + 27 ≤ #(B \ K) := hg.2.2.2.2.2.1
  have hthreshold : ∀ a ∈ A \ C, (2 : ℤ) ≤ -row q G B K a := by
    intro a ha
    have hh := (hg.2.2.2.2.2.2 a ha).2
    omega
  have hmin : ∀ P ⊆ B \ K, P.Nonempty → 2 ≤ extensionCost q 2 G A B K P := by
    intro P hP hne
    have hh := hK.cost_min P hP hne
    by_contra! hbad
    exact hnone ⟨P, hP, hne, by omega⟩
  have hpool : (ec G C (B \ K) : ℤ) + ec G (A \ C) K +
      deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤ 5 * q - 32 := by omega
  obtain ⟨z, hzR, _, hzgood⟩ := residual_uncovered (ban := ∅) hi ho hK.positive.1 hK.positive.2.1
    2 (5 * (q : ℤ) - 32) 2 2 4 0 (by norm_num) (by omega) hkc (by norm_num)
    hmin hthreshold hpool (empty_subset _) (by simp) (by omega) (by norm_num; omega)
    (by norm_num; omega) (by norm_num; omega) (by omega) (by omega)
  exact ⟨z, hzR, avoidance_from_residual hK.positive.1 (ell := 2) (by omega) hmin hzR hzgood⟩

/-- H5 surplus two: one SAME original omitted pair pays every original cut. -/
theorem Input.common_omission_two {q : ℕ} {A B : Finset V} (hi : Input q 2 G A B) :
    ∃ O : Finset V, O ⊆ B ∧ #O = 2 ∧ ∀ T ⊆ B, O ⊆ T → thetaJ q 2 G A B T ≤ 0 := by
  have hq := hi.q_large
  by_cases hex : ∃ T, LargePositive q 2 G A B T
  · obtain ⟨K, hK⟩ := exists_greatest_high hi hex
    have hKl := hK.positive.2.1
    have hKp := hK.positive.2.2
    have hKh := hi.theta_large_le hK.positive.1 hKl
    have hKne : K.Nonempty := card_pos.mp (by omega)
    have hcases : thetaJ q 2 G A B K = 1 ∨ thetaJ q 2 G A B K = 2 ∨ thetaJ q 2 G A B K = 3 := by omega
    rcases hcases with hheight | hheight | hheight
    · have hs := hi.positive_shape hK.positive.1 hKl hKp
      dsimp only at hs
      have hRne : (B \ K).Nonempty := card_pos.mp (by
        have hc := card_sdiff_add_card_eq_card hK.positive.1
        omega)
      obtain ⟨x, hxK⟩ := hKne
      obtain ⟨z, hzR⟩ := hRne
      have hne : x ≠ z := fun he => (mem_sdiff.mp hzR).2 (he ▸ hxK)
      apply hi.omission_pair (hK.positive.1 hxK) (mem_sdiff.mp hzR).1 hne
      intro T hT _ hzT
      exact (mem_sdiff.mp hzR).2 (hK.height_one_contains hheight hT hzT)
    · have hmax : ∀ N ⊆ B, K ⊆ N → K ≠ N → thetaJ q 2 G A B N ≤ 1 := by
        intro N hN hKN hne
        have hh := hK.strict_height N hN hKN hne
        omega
      obtain ⟨z, hzR, hext⟩ := local_two_uncovered hi hK.positive.1 hKl hheight hmax
      obtain ⟨x, hxK⟩ := hKne
      have hne : x ≠ z := fun he => (mem_sdiff.mp hzR).2 (he ▸ hxK)
      have havoid := avoid_all_large_from_extensions hi hK hext
      apply hi.omission_pair (hK.positive.1 hxK) (mem_sdiff.mp hzR).1 hne
      intro T hT _
      exact havoid T hT
    · by_cases hone : ∃ P ⊆ B \ K, P.Nonempty ∧ extensionCost q 2 G A B K P = 1
      · obtain ⟨P, hP, hPne, hPc⟩ := hone
        obtain ⟨H, _, hH⟩ := exists_max_petal_extension hK.cost_min hP hPne hPc
        let T0 := K ∪ H
        have hT0sub : T0 ⊆ B := union_subset hK.positive.1 (hH.1.trans sdiff_subset)
        have hT0large : q - 1 ≤ #T0 := hKl.trans (card_le_card subset_union_left)
        have hT0height : thetaJ q 2 G A B T0 = 2 := by
          change thetaJ q 2 G A B (K ∪ H) = 2
          have hc := hH.2.2.1
          unfold extensionCost at hc
          omega
        have hT0max : ∀ N ⊆ B, T0 ⊆ N → T0 ≠ N → thetaJ q 2 G A B N ≤ 1 := by
          intro N hN hTN hne
          have hh := hH.strict_theta hK.positive.1 N hN hTN hne
          omega
        obtain ⟨z, hzR, hzgood⟩ := local_two_uncovered hi hT0sub hT0large hT0height hT0max
        obtain ⟨x, hxH⟩ := hH.2.1
        have hxT0 : x ∈ T0 := mem_union_right _ hxH
        have hxB := hT0sub hxT0
        have hzB := (mem_sdiff.mp hzR).1
        have hne : x ≠ z := fun he => (mem_sdiff.mp hzR).2 (he ▸ hxT0)
        apply hi.omission_pair hxB hzB hne
        intro T hT hxT hzT
        obtain ⟨M, hTM, hM⟩ := exists_max_large_extension q 2 hT
        have hKM := hK.subset_max hi hM
        have hxM := hTM hxT
        have hzM := hTM hzT
        have hT0M : T0 ⊆ M := by
          by_contra hn
          have hneU : M ≠ M ∪ T0 := by
            intro he
            exact hn (by simpa only [← he] using (subset_union_right : T0 ⊆ M ∪ T0))
          have hU := hM.2 (M ∪ T0) (union_subset hM.1.1 hT0sub) subset_union_left hneU
          have hKI : K ⊆ M ∩ T0 := subset_inter hKM subset_union_left
          have hneI : K ≠ M ∩ T0 := by
            intro he
            have hxI : x ∈ M ∩ T0 := mem_inter.mpr ⟨hxM, hxT0⟩
            have hxK : x ∈ K := by rw [he]; exact hxI
            exact (mem_sdiff.mp (hH.1 hxH)).2 hxK
          have hI := hK.strict_height (M ∩ T0) (inter_subset_left.trans hM.1.1) hKI hneI
          have hsuper := Input.theta_supermod (G := G) q 2 A B M T0
          have hMp := hM.1.2.2
          omega
        exact hzgood M hM.1.1 hT0M hM.1.2.2 hzM
      · obtain ⟨z, hzR, hext⟩ := high_three_without_one hi hK hheight hone
        obtain ⟨x, hxK⟩ := hKne
        have hne : x ≠ z := fun he => (mem_sdiff.mp hzR).2 (he ▸ hxK)
        have havoid := avoid_all_large_from_extensions hi hK hext
        apply hi.omission_pair (hK.positive.1 hxK) (mem_sdiff.mp hzR).1 hne
        intro T hT _
        exact havoid T hT
  · have hB := hi.shores_large.2
    obtain ⟨x, hx⟩ := card_pos.mp (show 0 < #B by omega)
    have hcard := card_erase_of_mem hx
    obtain ⟨z, hz⟩ := card_pos.mp (show 0 < #(B.erase x) by omega)
    have hzB := (mem_erase.mp hz).2
    have hne : x ≠ z := fun he => (mem_erase.mp hz).1 he.symm
    apply hi.omission_pair hx hzB hne
    intro T hT _ _
    exact hex ⟨T, hT⟩

/-- H6 all original cuts are paid by one common omission, in both literal branches. -/
theorem Input.common_omission {q j : ℕ} {A B : Finset V} (hi : Input q j G A B) :
    ∃ O : Finset V, O ⊆ B ∧ #O = j ∧ ∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0 := by
  rcases hi.branch with hj | hj
  · subst j
    obtain ⟨z, hzB, hzgood⟩ := hi.common_omission_one
    refine ⟨{z}, singleton_subset_iff.mpr hzB, card_singleton z, ?_⟩
    intro T hT hOT
    exact hzgood T hT (hOT (mem_singleton_self z))
  · subst j
    exact hi.common_omission_two

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The entire original H3 unequal endpoint, with no supplied selector or factor. -/
theorem h3_unequal : H3UnequalClaim.{u} := by
  intro q j V instV G A B hOriginal
  classical
  have hi := hOriginal.to_input
  obtain ⟨O, hO, hOj, hcuts⟩ := hi.common_omission
  have hf := factor_of_common_omission q j hi.card hO hOj hcuts
  have hq : 0 < q := by have hlarge := hOriginal.q_large; omega
  have hA : A.Nonempty := card_pos.mp (by have hs := hi.shores_large.1; omega)
  have hdis : Disjoint A (B \ O) := hOriginal.disjoint.mono Subset.rfl sdiff_subset
  obtain ⟨H, hverts, hnonempty, hregular⟩ := factor_exact_subgraph hq hA hdis hf
  exact ⟨O, hO, hOj, hf, H, hverts, hnonempty, hregular⟩

end Erdos585.H3Unequal
