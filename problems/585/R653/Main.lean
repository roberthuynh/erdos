import Openmath.AllHTopCritical.Original

/-! R642 all-cut original-host argument, independently reconstructed in R646. -/
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.AllCutRigidityR653
open QB4 B5 L34 H3Unequal AllHTopCritical
universe u
variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V} {q : ℕ} {A B X Y : Finset V}

/-- Actual original rectangles of the arbitrary input cut. -/
structure Conclusion (q : ℕ) (G : SimpleGraph V) (A B X Y : Finset V) : Prop where
  imbalance : (#X : ℤ) + #Y - #B = 2
  forward : (ec G X Y : ℤ) = 2 * (q : ℤ) - 1
  reverse : (ec G (A \ X) (B \ Y) : ℤ) = (q : ℤ) - 29
  scar_A : deficiency (2 * (q : ℤ) - 2) G B (A \ X) = 0
  scar_B : deficiency (2 * (q : ℤ) - 2) G A (B \ Y) = 0
  first_deficit : coreDefect q G X (B \ Y) = (constant 3 q : ℤ) + 1
  second_deficit : coreDefect q G (A \ X) Y = (constant 3 q : ℤ) + 1
  first_eligible : 2 * q ≤ #X + #(B \ Y)
  second_eligible : 2 * q ≤ #(A \ X) + #Y
  first_proper : #X + #(B \ Y) < Fintype.card V
  second_proper : #(A \ X) + #Y < Fintype.card V
  first_actual_support : 2 * q ≤ #(X ∪ (B \ Y)) ∧
    #(X ∪ (B \ Y)) < Fintype.card V
  second_actual_support : 2 * q ≤ #((A \ X) ∪ Y) ∧
    #((A \ X) ∪ Y) < Fintype.card V
  saturated_A : ∀ v ∈ A \ X, G.degree v = 2 * q - 2
  saturated_B : ∀ v ∈ B \ Y, G.degree v = 2 * q - 2

lemma rectangle_lower (host : Host 3 q G A B) (hX : X ⊆ A) (hY : Y ⊆ B) :
    (q : ℤ) * #X ≤ (#X : ℤ) * #(B \ Y) + (ec G X Y : ℤ) := by
  have hm := Bq.ec_lower_of_min (G := G) hX host.minA
  have hs := ec_sdiff_add_right (G := G) hY X
  have hp := AllHTopCritical.ec_le_product (G := G) X (B \ Y)
  zify at hm hs hp
  nlinarith

/-- Every floor uses its actual original order guard. No canonical cut is supplied. -/
theorem all_violating_cuts (host : Host 3 q G A B)
    (hX : X ⊆ A) (hY : Y ⊆ B)
    (violation : (ec G X Y : ℤ) <
      (q : ℤ) * ((#X : ℤ) + #Y - #B)) : Conclusion q G A B X Y := by
  let k : ℤ := (#X : ℤ) + #Y - #B
  let dA := deficiency (2 * (q : ℤ) - 2) G B (A \ X)
  let dB := deficiency (2 * (q : ℤ) - 2) G A (B \ Y)
  have hq : (16384 : ℤ) ≤ q := by
    have hp := host.parameters.large
    norm_num at hp
    exact_mod_cast hp
  have hc : (constant 3 q : ℤ) = 3 * (q : ℤ) - 32 := by
    have hh := host.parameters.constant_cast
    norm_num [offset] at hh
    exact hh
  have ca := card_sdiff_add_card_eq_card hX
  have cb := card_sdiff_add_card_eq_card hY
  have bal := host.balanced
  have ord := host.shore_order
  zify at ca cb bal ord
  have kX : (#X : ℤ) = #(B \ Y) + k := by dsimp [k]; omega
  have kY : (#Y : ℤ) = #(A \ X) + k := by dsimp [k]; omega
  have da0 : 0 ≤ dA := deficiency_nonneg _
    (fun v hv => host.capA_int v (sdiff_subset hv))
  have db0 : 0 ≤ dB := deficiency_nonneg _
    (fun v hv => host.capB_int v (sdiff_subset hv))
  have sx := ec_sdiff_add_right (G := G) hY X
  have sv := ec_sdiff_add_right (G := G) hY (A \ X)
  have sa := ec_sdiff_add_left (G := G) hX B
  have st := ec_sdiff_add_left (G := G) hX (B \ Y)
  have da := deficiency_eq (G := G) (2 * (q : ℤ) - 2) B (A \ X)
  have db := deficiency_eq (G := G) (2 * (q : ℤ) - 2) A (B \ Y)
  rw [ec_comm (G := G) (B \ Y) A] at db
  have whole := host.deficiency_A
  rw [deficiency_eq, hc] at whole
  zify at sx sv sa st
  change dA = _ at da
  change dB = _ at db
  have identity : 3 * (q : ℤ) - 32 =
      2 * ((q : ℤ) - 1) * k + (ec G (A \ X) (B \ Y) : ℤ) +
        dA + dB - (ec G X Y : ℤ) := by
    nlinarith
  have x0 : 0 ≤ (ec G X Y : ℤ) := Nat.cast_nonneg _
  have z0 : 0 ≤ (ec G (A \ X) (B \ Y) : ℤ) := Nat.cast_nonneg _
  change (ec G X Y : ℤ) < (q : ℤ) * k at violation
  have kp : 1 ≤ k := by
    by_contra! hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ q by omega)
      (show k ≤ 0 by omega)
    nlinarith only [hm, violation, x0]
  have kle : k ≤ 2 := by
    by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ) - 2 by omega)
      (show 0 ≤ k - 3 by omega)
    nlinarith only [identity, violation, hm, da0, db0, z0, hq]
  have lowerX := rectangle_lower host hX hY
  have lowerY : (q : ℤ) * #Y ≤ (#Y : ℤ) * #(A \ X) + (ec G X Y : ℤ) := by
    have hm := Bq.ec_lower_of_min (G := G) hY host.minB
    have hs := ec_sdiff_add_right (G := G) hX Y
    have hp := AllHTopCritical.ec_le_product (G := G) Y (A \ X)
    rw [ec_comm (G := G) Y X] at hs
    zify at hm hs hp
    nlinarith
  have Xlarge : (q : ℤ) + 1 ≤ #X := by
    by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (#X : ℤ) - k by omega)
      (show 0 ≤ (q : ℤ) - #X by omega)
    nlinarith only [lowerX, kX, violation, hm]
  have Ylarge : (q : ℤ) + 1 ≤ #Y := by
    by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (#Y : ℤ) - k by omega)
      (show 0 ≤ (q : ℤ) - #Y by omega)
    nlinarith only [lowerY, kY, violation, hm]
  have eligible1 : 2 * q ≤ #X + #(B \ Y) := by omega
  have eligible2 : 2 * q ≤ #(A \ X) + #Y := by omega
  have proper1 : #X + #(B \ Y) < Fintype.card V := by omega
  have proper2 : #(A \ X) + #Y < Fintype.card V := by omega
  have floor1 := host.paired_floor hX (sdiff_subset : B \ Y ⊆ B) eligible1 proper1
  have floor2 := host.paired_floor (sdiff_subset : A \ X ⊆ A) hY eligible2 proper2
  rw [hc] at floor1 floor2
  have diagonal1 : coreDefect q G X (B \ Y) =
      ((q : ℤ) - 1) * k + (ec G (A \ X) (B \ Y) : ℤ) + dB := by
    unfold coreDefect
    nlinarith only [kX, db, st]
  have diagonal2 : coreDefect q G (A \ X) Y =
      ((q : ℤ) - 1) * k + (ec G (A \ X) (B \ Y) : ℤ) + dA := by
    unfold coreDefect
    nlinarith only [kY, da, sv]
  rw [diagonal1] at floor1
  rw [diagonal2] at floor2
  have keq : k = 2 := by
    by_contra hn
    have hk : k = 1 := by omega
    rw [hk] at identity violation floor1 floor2
    nlinarith only [identity, violation, floor1, floor2, da0, db0]
  have rigidity : (ec G X Y : ℤ) = 2 * (q : ℤ) - 1 ∧
      (ec G (A \ X) (B \ Y) : ℤ) = (q : ℤ) - 29 ∧ dA = 0 ∧ dB = 0 := by
    rw [keq] at identity violation floor1 floor2
    constructor
    · nlinarith only [identity, violation, floor1, floor2, da0, db0]
    constructor
    · nlinarith only [identity, violation, floor1, floor2, da0, db0]
    constructor <;> nlinarith only [identity, violation, floor1, floor2, da0, db0]
  refine ⟨keq, rigidity.1, rigidity.2.1, rigidity.2.2.1, rigidity.2.2.2,
    ?_, ?_, eligible1, eligible2, proper1, proper2, ?_, ?_, ?_, ?_⟩
  · rw [diagonal1, keq, rigidity.2.1, rigidity.2.2.2, hc]
    ring
  · rw [diagonal2, keq, rigidity.2.1, rigidity.2.2.1, hc]
    ring
  · rw [card_union_of_disjoint (host.disjoint.mono hX sdiff_subset)]
    exact ⟨eligible1, proper1⟩
  · rw [card_union_of_disjoint (host.disjoint.mono sdiff_subset hY)]
    exact ⟨eligible2, proper2⟩
  · intro v hv
    have hz : deficiency ((2 * q - 2 : ℕ) : ℤ) G B (A \ X) = 0 := by
      have cast : ((2 * q - 2 : ℕ) : ℤ) = 2 * (q : ℤ) - 2 := by omega
      rw [cast]
      exact rigidity.2.2.1
    have hd := saturated_of_zero (fun w hw => host.capA w (sdiff_subset hw)) hz hv
    rw [dg_eq_degree host.bipartite (sdiff_subset hv)] at hd
    exact hd
  · intro v hv
    have hz : deficiency ((2 * q - 2 : ℕ) : ℤ) G A (B \ Y) = 0 := by
      have cast : ((2 * q - 2 : ℕ) : ℤ) = 2 * (q : ℤ) - 2 := by omega
      rw [cast]
      exact rigidity.2.2.2
    have hd := saturated_of_zero (fun w hw => host.capB w (sdiff_subset hw)) hz hv
    rw [dg_eq_degree host.bipartite.symm (sdiff_subset hv)] at hd
    exact hd

#check @all_violating_cuts
#print axioms all_violating_cuts
end Erdos585.AllCutRigidityR653
