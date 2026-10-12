import R882.Positive.Tiny
import AllHNextNonstrict.TopEscape

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.R882.Positive
open QB4 B5 L34 H3Unequal
open AllHNextNonstrict.TopEscape
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exact rectangular original-incidence cancellation across two exclusive cells. -/
lemma exclusive_ec (C D T U : Finset V) :
    ec G C T + ec G D U = ec G (C\D) (T\U) + ec G (D\C) (U\T) +
      ec G (C∩D) (T∪U) + ec G (C∪D) (T∩U) := by
  have c := ec_sdiff_add_left (G:=G) (inter_subset_left : C∩D ⊆ C) T
  have d := ec_sdiff_add_left (G:=G) (inter_subset_right : C∩D ⊆ D) U
  have t := ec_sdiff_add_right (G:=G) (inter_subset_left : T∩U ⊆ T) (C\D)
  have u := ec_sdiff_add_right (G:=G) (inter_subset_right : T∩U ⊆ U) (D\C)
  have i := ec_modular (G:=G) (C∩D) T U
  have r := ec_modular (G:=G) (T∩U) C D
  have c' := ec_sdiff_add_left (G:=G) (inter_subset_left : C∩D ⊆ C) (T∩U)
  have d' := ec_sdiff_add_left (G:=G) (inter_subset_right : C∩D ⊆ D) (T∩U)
  have cd : C\(C∩D)=C\D := by ext v; simp
  have dc : D\(C∩D)=D\C := by ext v; simp
  have tu : T\(T∩U)=T\U := by ext v; simp
  have ut : U\(T∩U)=U\T := by ext v; simp
  rw [cd] at c c'
  rw [dc] at d d'
  rw [tu] at t
  rw [ut] at u
  simp only [ec_comm (G:=G) (T∩U)] at r
  omega

namespace Data
variable {h q j e : ℕ} {A B : Finset V} (d : Data h q j e G A B)
include d

/-- R873's two-difference identity, in original paired shore coordinates.
The unequal-shore correction is already present in the total A scar. -/
lemma two_exclusive_identity {C D T U : Finset V}
    (hC : C⊆A) (hD : D⊆A) (hT : T⊆B) (hU : U⊆B)
    (optC : Optimizer q G A B T C) (optD : Optimizer q G A B U D) :
    coreDefect q G (C\D) (T\U) + coreDefect q G (D\C) (U\T) =
      (h : ℤ)*q-offset h e-((q : ℤ)-1)*j + 2*(q : ℤ)*j -
      thetaJ q j G A B T-thetaJ q j G A B U +
      ((#C : ℤ)-#T)+((#D : ℤ)-#U) -
      deficiency (2*(q : ℤ)-2) G A (T∩U) -
      deficiency (2*(q : ℤ)-2) G B (A\(C∪D)) -
      ec G (C∩D) (B\(T∪U)) - ec G (A\(C∪D)) (T∩U) := by
  have he := exclusive_ec (G:=G) C D T U
  have hr := ec_sdiff_add_right (G:=G) (union_subset hT hU) (C∩D)
  have hc := ec_sdiff_add_left (G:=G) (union_subset hC hD) (T∩U)
  have hs := sum_union_inter (s₁:=C) (s₂:=D)
    (f:=fun v => 2*(q : ℤ)-2-(dg G B v : ℤ))
  have ha := sum_sdiff (s₁:=C∪D) (s₂:=A)
    (f:=fun v => 2*(q : ℤ)-2-(dg G B v : ℤ)) (union_subset hC hD)
  have ct := card_sdiff_add_card_eq_card (inter_subset_left : C∩D⊆C)
  have dt := card_sdiff_add_card_eq_card (inter_subset_right : C∩D⊆D)
  have tt := card_sdiff_add_card_eq_card (inter_subset_left : T∩U⊆T)
  have ut := card_sdiff_add_card_eq_card (inter_subset_right : T∩U⊆U)
  have cd : C\(C∩D)=C\D := by ext v; simp
  have dc : D\(C∩D)=D\C := by ext v; simp
  have tu : T\(T∩U)=T\U := by ext v; simp
  have uu : U\(T∩U)=U\T := by ext v; simp
  rw [cd] at ct
  rw [dc] at dt
  rw [tu] at tt
  rw [uu] at ut
  have pC := optC.theta_eq (j:=j)
  have pD := optD.theta_eq (j:=j)
  rw [row_sum] at pC pD
  have total := d.deficient
  change deficiency (2*(q : ℤ)-2) G B (C∪D) +
    deficiency (2*(q : ℤ)-2) G B (C∩D) =
    deficiency (2*(q : ℤ)-2) G B C+deficiency (2*(q : ℤ)-2) G B D at hs
  change deficiency (2*(q : ℤ)-2) G B (A\(C∪D)) +
    deficiency (2*(q : ℤ)-2) G B (C∪D) = deficiency (2*(q : ℤ)-2) G B A at ha
  simp only [deficiency_eq] at hs ha total ⊢
  rw [ec_comm (G:=G) (T∩U) A]
  unfold coreDefect
  zify at he hr hc ct dt tt ut
  nlinarith

/-- Two eligible exclusive original supports rule out a tiny column intersection. -/
lemma large_intersection {T U : Finset V}
    (hT : T ⊆ B) (hTl : q - 1 ≤ #T) (hTp : 0 < thetaJ q j G A B T)
    (hU : U ⊆ B) (hUl : q - 1 ≤ #U) (hUp : 0 < thetaJ q j G A B U) :
    q - 1 ≤ #(T ∩ U) := by
  have hq := d.parameters.q_ge_height
  have hh := d.parameters.height_int
  have hj := d.parameters.j_bounds
  have hn := d.parameters.numeric
  have he := d.parameters.geometry_numeric
  have hcup := d.theta_large_le (union_subset hT hU)
    (hTl.trans (card_le_card subset_union_left))
  by_contra! hbad
  have hsmall : #(T ∩ U) ≤ q - 2 := by omega
  by_cases htiny : #(T ∩ U) < h
  · let C := canonical q G A B T
    let D := canonical q G A B U
    have hC : C⊆A := canonical_subset q A B T
    have hD : D⊆A := canonical_subset q A B U
    have optC : Optimizer q G A B T C := strict_optimizer q A B T
    have optD : Optimizer q G A B U D := strict_optimizer q A B U
    have shapeC := d.positive_shape optC hT hTl hTp
    have shapeD := d.positive_shape optD hU hUl hUp
    dsimp only at shapeC shapeD
    have ct := card_sdiff_add_card_eq_card (inter_subset_left : T∩U⊆T)
    have cu := card_sdiff_add_card_eq_card (inter_subset_right : T∩U⊆U)
    have tu : T\(T∩U)=T\U := by ext v; simp
    have ut : U\(T∩U)=U\T := by ext v; simp
    rw [tu] at ct
    rw [ut] at cu
    have cA := card_le_card (sdiff_subset.trans hC : C\D⊆A)
    have dA := card_le_card (sdiff_subset.trans hD : D\C⊆A)
    have tB := card_le_card (sdiff_subset.trans hT : T\U⊆B)
    have uB := card_le_card (sdiff_subset.trans hU : U\T⊆B)
    have tlt : #(T\U)<#B := by omega
    have ult : #(U\T)<#B := by omega
    have floorC := d.sparse (C\D) (sdiff_subset.trans hC) (T\U)
      (sdiff_subset.trans hT) (by omega) (by omega)
    have floorD := d.sparse (D\C) (sdiff_subset.trans hD) (U\T)
      (sdiff_subset.trans hU) (by omega) (by omega)
    have twiceC := twice_coreDefect (G:=G) q (C\D) (T\U)
    have twiceD := twice_coreDefect (G:=G) q (D\C) (U\T)
    have id := d.two_exclusive_identity hC hD hT hU optC optD
    have scarA := d.scar_nonneg (sdiff_subset : A\(C∪D)⊆A)
    have scarB : 0≤deficiency (2*(q : ℤ)-2) G A (T∩U) :=
      deficiency_nonneg _ fun v hv => d.capB_int (hT (mem_inter.mp hv).1)
    have cross1 : (0 : ℤ)≤ec G (C∩D) (B\(T∪U)) := Nat.cast_nonneg _
    have cross2 : (0 : ℤ)≤ec G (A\(C∪D)) (T∩U) := Nat.cast_nonneg _
    have ha := d.parameters.offset_cast
    have eb := d.parameters.error_int
    have prod := mul_nonneg (show 0≤(h : ℤ)-j-1 by omega) (Nat.cast_nonneg q : (0 : ℤ)≤q)
    nlinarith only [floorC,floorD,twiceC,twiceD,id,scarA,scarB,cross1,cross2,
      ha,eb,prod,shapeC.2.2.2.1,shapeD.2.2.2.1,hTp,hUp,hj.2,he.1]
  · have hinter := d.theta_intermediate (by omega) hsmall
    have hsuper := H3Unequal.Input.theta_supermod (G := G) q j A B T U
    omega

end Data
end Erdos585.R882.Positive
