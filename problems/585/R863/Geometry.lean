import R863.Numeric

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.R863
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Data
variable {h q j e : ℕ} {A B : Finset V} (d : Data h q j e G A B)
include d

omit [DecidableEq V] in
lemma capA_int {a : V} (ha : a ∈ A) : (dg G B a : ℤ) ≤ 2 * (q : ℤ) - 2 := by
  have hd := d.capA a ha
  have hq := d.parameters.q_pos
  omega

omit [DecidableEq V] in
lemma capB_int {b : V} (hb : b ∈ B) : (dg G A b : ℤ) ≤ 2 * (q : ℤ) - 2 := by
  have hd := d.capB b hb
  have hq := d.parameters.q_pos
  omega

lemma scar_nonneg {X : Finset V} (hX : X ⊆ A) :
    0 ≤ deficiency (2 * (q : ℤ) - 2) G B X :=
  deficiency_nonneg _ fun _a ha => d.capA_int (hX ha)

lemma scar_le {X : Finset V} (hX : X ⊆ A) :
    deficiency (2 * (q : ℤ) - 2) G B X ≤
      (h : ℤ) * q - offset h e - ((q : ℤ) - 1) * j := by
  calc _ ≤ deficiency (2 * (q : ℤ) - 2) G B A :=
      deficiency_le_subset _ hX fun _a ha => d.capA_int ha
    _ = _ := d.deficient

lemma scar_split {X : Finset V} (hX : X ⊆ A) :
    deficiency (2 * (q : ℤ) - 2) G B (A \ X) +
      deficiency (2 * (q : ℤ) - 2) G B X =
      (h : ℤ) * q - offset h e - ((q : ℤ) - 1) * j := by
  rw [← d.deficient]
  exact sum_sdiff hX

lemma row_scar_le {a : V} (ha : a ∈ A) : 2 * (q : ℤ) - 2 - dg G B a ≤
    (h : ℤ) * q - offset h e - ((q : ℤ) - 1) * j := by
  have hs := d.scar_le (singleton_subset_iff.mpr ha)
  simpa [deficiency] using hs

omit [DecidableEq V] in
lemma shores_large : q ≤ #A ∧ q + j ≤ #B := by
  have hj := d.parameters.j_pos
  have hbn : B.Nonempty := card_pos.mp (by have hc := d.card; omega)
  obtain ⟨b, hb⟩ := hbn
  have hd := d.minB b hb
  have hc := dg_le_card (G := G) A b
  have hi := d.card
  omega

omit [DecidableEq V] in
lemma theta_full : thetaJ q j G A B B = 0 := by
  simp only [thetaJ, theta, row, sub_self, zero_add,
    max_eq_right (Nat.cast_nonneg q), sum_const, nsmul_eq_mul]
  rw [d.card]
  push_cast
  ring

omit [DecidableEq V] in
lemma theta_empty : thetaJ q j G A B ∅ = (q : ℤ) * j := by
  have hz : ∀ a ∈ A, max 0 (row q G B ∅ a) = 0 := by
    intro a ha
    have hm := d.minA a ha
    have he : dg G ∅ a = 0 := by simp [dg]
    rw [row, he]
    simp only [Nat.cast_zero, zero_sub]
    omega
  simp only [thetaJ, theta, card_empty, Nat.cast_zero, mul_zero, sub_zero]
  rw [sum_eq_zero hz]
  ring

omit [DecidableEq V] in
lemma edge_cap_T {X T : Finset V} (hX : X ⊆ A) (hT : T ⊆ B) :
    (ec G X T : ℤ) ≤ (2 * (q : ℤ) - 2) * #T := by
  rw [ec_comm, ec, Nat.cast_sum]
  calc
    _ ≤ ∑ _b ∈ T, (2 * (q : ℤ) - 2) := by
      refine sum_le_sum fun b hb => ?_
      have hd := dg_mono (G := G) hX b
      have hc := d.capB_int (hT hb)
      omega
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

lemma optimizer_proper {K C : Finset V} (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hp : 0 < thetaJ q j G A B K) : #C < #A := by
  have hne : C ≠ A := by
    intro heq
    have hc := card_sdiff_add_card_eq_card hK
    have he := ec_sdiff_add_right (G := G) hK A
    have hm := Bq.ec_lower_of_min (G := G) (sdiff_subset : B \ K ⊆ B) d.minB
    rw [ec_comm] at hm
    have ht := opt.theta_eq (j := j)
    rw [heq, row_sum] at ht
    have hcard := d.card
    zify at hc he hm hcard
    nlinarith
  exact card_lt_card ⟨opt.subset, fun hh => hne (Subset.antisymm opt.subset hh)⟩

/-- Every positive original test leaves at least q+1 original opposite-shore vertices. -/
lemma positive_complement {T : Finset V} (hT : T ⊆ B)
    (hp : 0 < thetaJ q j G A B T) : q + 1 ≤ #(B \ T) := by
  have hopt := weak_optimizer (G := G) q A B T
  have hc := d.optimizer_proper hopt hT hp
  have hn : (A \ weakCore q G A B T).Nonempty := by
    apply card_pos.mp
    have hh := card_sdiff_add_card_eq_card hopt.subset
    omega
  obtain ⟨a, ha⟩ := hn
  have hr := weak_outside_strict (G := G) q A B T ha
  have hd := dg_sdiff_add (G := G) hT a
  have hb := dg_le_card (G := G) (B \ T) a
  unfold row at hr
  omega

/-- Every actual optimizing core, including equality rows, pays its eligible proper floor. -/
lemma positive_shape {K C : Finset V} (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hlarge : q - 1 ≤ #K) (hp : 0 < thetaJ q j G A B K) :
    let k : ℤ := (#C : ℤ) - #K
    let ε := coreDefect q G C K - ((h : ℤ) * q - offset h e - e + 1)
    #K < #B ∧ #C < #A ∧ 1 - (j : ℤ) ≤ k ∧ k ≤ (h : ℤ) - 1 ∧
      thetaJ q j G A B K ≤ j + (h : ℤ) + e - 2 ∧ 0 ≤ ε ∧
      ε + deficiency (2 * (q : ℤ) - 2) G B (A \ C) =
        j + k - thetaJ q j G A B K + e - 1 := by
  dsimp only
  let k : ℤ := (#C : ℤ) - #K
  have hq := d.parameters.q_ge_height
  have hn := d.parameters.numeric
  have hj := d.parameters.j_bounds
  have hclt := d.optimizer_proper opt hK hp
  have hkle := card_le_card hK
  have hlt : #K < #B := by
    apply card_lt_card
    refine ⟨hK, ?_⟩
    intro hBK
    have he : K = B := Subset.antisymm hK hBK
    rw [he, d.theta_full] at hp
    omega
  have hal := d.scar_le opt.subset
  have han := d.scar_nonneg opt.subset
  have hsp := d.sparse C opt.subset K hK (by omega) (by omega)
  have ht := opt.theta_potential (j := j)
  have he := d.edge_cap_T opt.subset hK
  have hsigma : 0 ≤ deficiency (2 * (q : ℤ) - 2) G A K :=
    deficiency_nonneg _ fun _b hb => d.capB_int (hK hb)
  have hcross := opt.cross_scar_identity (j := j)
  have hk : k ≤ (h : ℤ) - 1 := by
    by_contra! hbad
    have hprod : 0 ≤ ((q : ℤ) - 2) * (k - h) := mul_nonneg (by omega) (by omega)
    dsimp [k] at hprod
    nlinarith [show (0 : ℤ) ≤ ec G (A \ C) K from Nat.cast_nonneg _]
  have hε : 0 ≤ coreDefect q G C K - ((h : ℤ) * q - offset h e - e + 1) := by
    have hh := twice_coreDefect (G := G) q C K
    omega
  have hsplit := d.scar_split opt.subset
  have hid : coreDefect q G C K - ((h : ℤ) * q - offset h e - e + 1) +
      deficiency (2 * (q : ℤ) - 2) G B (A \ C) =
        j + k - thetaJ q j G A B K + e - 1 := by
    have hh := twice_coreDefect (G := G) q C K
    dsimp [k]
    nlinarith
  have hout := d.scar_nonneg (sdiff_subset : A \ C ⊆ A)
  have hklo : 1 - (j : ℤ) ≤ k := by
    have hne := opt.theta_eq (j := j)
    rw [row_sum] at hne
    have hpart := ec_sdiff_add_right (G := G) hK C
    zify at hpart
    by_contra! hbad
    have hprod : (q : ℤ) * (j + k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by omega)
    dsimp [k] at hprod
    nlinarith only [hprod, hne, hpart, hp, show (0 : ℤ) ≤ ec G C (B \ K) from Nat.cast_nonneg _]
  exact ⟨hlt, hclt, hklo, hk, by omega, hε, hid⟩

lemma outside_scar_le {K C : Finset V} (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hlarge : q - 1 ≤ #K) (hp : 0 < thetaJ q j G A B K) :
    deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤ 2 * (h : ℤ) + e - 4 := by
  have hs := d.positive_shape opt hK hlarge hp
  have hj := d.parameters.j_bounds
  dsimp only at hs
  omega

lemma optimizer_internal_min {K C : Finset V} (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hlarge : q - 1 ≤ #K) (hp : 0 < thetaJ q j G A B K)
    {a : V} (ha : a ∈ C) :
    (q : ℤ) - 1 - (coreDefect q G C K - ((h : ℤ) * q - offset h e - e + 1)) ≤ dg G K a := by
  have hs := d.positive_shape opt hK hlarge hp
  dsimp only at hs
  have hq := d.parameters.q_ge_height
  have hsp := d.sparse (C.erase a) ((erase_subset _ _).trans opt.subset) K hK
    (by omega) (by have hc := card_le_card (erase_subset a C); omega)
  have hi := potential_erase_left (G := G) (2 * (q : ℤ) - 2) ha K
  have hh := twice_coreDefect (G := G) q C K
  rw [hi] at hsp
  omega

lemma optimizer_internal_min_coarse {K C : Finset V} (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hlarge : q - 1 ≤ #K) (hp : 0 < thetaJ q j G A B K)
    {a : V} (ha : a ∈ C) : (q : ℤ) - 2 * h - e + 3 ≤ dg G K a := by
  have hi := d.optimizer_internal_min opt hK hlarge hp ha
  have hs := d.positive_shape opt hK hlarge hp
  have hout := d.scar_nonneg (sdiff_subset : A \ C ⊆ A)
  have hj := d.parameters.j_bounds
  dsimp only at hs
  omega

lemma theta_large_le {T : Finset V} (hT : T ⊆ B) (hlarge : q - 1 ≤ #T) :
    thetaJ q j G A B T ≤ j + (h : ℤ) + e - 2 := by
  by_cases hp : 0 < thetaJ q j G A B T
  · have hs := d.positive_shape (strict_optimizer q A B T) hT hlarge hp
    dsimp only at hs
    exact hs.2.2.2.2.1
  · have hj := d.parameters.j_bounds
    have hh := d.parameters.height_int
    omega

end Data
end Erdos585.R863
