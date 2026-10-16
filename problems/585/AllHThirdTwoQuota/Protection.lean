import AllHThirdTwoQuota.Geometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHThirdTwoQuota
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Data
variable {h q a j : ℕ} {A B : Finset V} (d : Data h q a j G A B)
include d

/-- Three actual fragile scars exceed the total ORIGINAL scar. -/
lemma fragile_card : #d.fragileRows≤2 := by
  have hlo : ((q:ℤ)-2*h+3)*#d.fragileRows≤
      deficiency (2*(q:ℤ)-2) G B d.fragileRows := by
    calc
      _ = ∑ _x∈d.fragileRows, ((q:ℤ)-2*h+3) := by simp [mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro x hx
        have hd := (d.mem_fragile.mp hx).2
        have hh := d.parameters.height
        omega
  have hhi := d.scar_le d.fragile_subset
  have hj := d.parameters.surplus_int
  have ha := d.parameters.lower_int
  have hn := d.parameters.numeric
  by_contra! hbad
  have hp : 0≤((q:ℤ)-2*h+3)*((#d.fragileRows:ℤ)-3) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- Every actual fragile row lies in EVERY positive large optimizer. -/
lemma fragile_in_optimizer {K C : Finset V} (opt : Optimizer q G A B K C)
    (hK : K⊆B) (hl : q-1≤#K) (hp : 0<thetaJ q j G A B K)
    {x : V} (hx : x∈d.fragileRows) : x∈C := by
  by_contra hn
  have hv : x∈A\C := mem_sdiff.mpr ⟨(d.mem_fragile.mp hx).1,hn⟩
  have hs := single_le_sum (f := fun v => 2*(q:ℤ)-2-dg G B v)
    (fun v hv => by have hc := d.capA_int (mem_sdiff.mp hv).1; omega) hv
  change 2*(q:ℤ)-2-dg G B x≤deficiency (2*(q:ℤ)-2) G B (A\C) at hs
  have ho := d.outside_scar_le opt hK hl hp
  have hd := (d.mem_fragile.mp hx).2
  have hq := d.parameters.numeric
  have hh := d.parameters.height
  omega

lemma neighbor_residual_card {K : Finset V} (hK : K⊆B)
    (hl : q-1≤#K) (hp : 0<thetaJ q j G A B K)
    {x : V} (hx : x∈d.fragileRows) : #(d.neighbors x\K)≤4*h-10 := by
  have opt := strict_optimizer (G:=G) q A B K
  have hroot := d.fragile_in_optimizer opt hK hl hp hx
  have hi := d.optimizer_internal_min_coarse opt hK hl hp hroot
  have hd := (d.mem_fragile.mp hx).2
  have hsplit := dg_sdiff_add (G:=G) hK x
  have he : d.neighbors x\K=(B\K).filter (fun z => G.Adj x z) := by
    ext z
    simp only [mem_sdiff,mem_filter,neighbors]
    tauto
  rw [he]
  change dg G (B\K) x≤4*h-10
  have hh := d.parameters.height
  omega

lemma protected_residual_card {K : Finset V} (hK : K⊆B)
    (hl : q-1≤#K) (hp : 0<thetaJ q j G A B K) : #(d.protectedCols\K)≤8*h-20 := by
  have he : d.protectedCols\K=d.fragileRows.biUnion (fun x => d.neighbors x\K) := by
    ext z
    simp only [protectedCols,mem_sdiff,mem_biUnion]
    tauto
  calc
    _ = #(d.fragileRows.biUnion (fun x => d.neighbors x\K)) := congrArg Finset.card he
    _ ≤ ∑ x∈d.fragileRows, #(d.neighbors x\K) := card_biUnion_le
    _ ≤ ∑ _x∈d.fragileRows, (4*h-10) :=
      sum_le_sum (fun x hx => d.neighbor_residual_card hK hl hp hx)
    _ = #d.fragileRows*(4*h-10) := by simp
    _ ≤ 2*(4*h-10) := Nat.mul_le_mul_right _ d.fragile_card
    _ = 8*h-20 := by have hh := d.parameters.height; omega

omit [DecidableEq V] in
/-- This is a degree/scar consequence, with no fragile hypothesis. -/
lemma shore_B_large : 2*q-4≤#B := by
  by_contra! hb
  have hqA := d.shores_large.1
  have hlow : (3:ℤ)*#A≤deficiency (2*(q:ℤ)-2) G B A := by
    calc
      _ = ∑ _v∈A, (3:ℤ) := by simp [mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro v _
        have hd := dg_le_card (G:=G) B v
        omega
  rw [d.deficient] at hlow
  have hs := d.parameters.scar_upper
  omega

/-- Padding outside BOTH full neighborhoods is available whenever a large test exists. -/
lemma allowed_card {K : Finset V} (hK : K⊆B) (hl : q-1≤#K)
    (hp : 0<thetaJ q j G A B K) : j≤#(B\d.protectedCols) := by
  have hR := d.positive_complement hK hp
  have hb := d.protected_residual_card hK hl hp
  have he : (B\K)\(d.protectedCols\K)=(B\K)\d.protectedCols := by
    ext z
    simp only [mem_sdiff]
    tauto
  have hcover : B\K⊆((B\K)\(d.protectedCols\K))∪(d.protectedCols\K) := by
    intro z hz
    by_cases hn : z∈d.protectedCols\K
    · exact mem_union_right _ hn
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hz,hn⟩)
  have hc := (card_le_card hcover).trans (card_union_le _ _)
  rw [he] at hc
  have hsub : (B\K)\d.protectedCols⊆B\d.protectedCols :=
    sdiff_subset_sdiff_left _ sdiff_subset
  have hle := card_le_card hsub
  have hn := d.parameters.numeric
  have hh := d.parameters.height_int
  have hj := d.parameters.surplus_int
  have h10 : (10:ℤ)*h<q := by nlinarith [sq_nonneg (h:ℤ)]
  omega

lemma quota_of_disjoint {O : Finset V} (hOB : O⊆B) (hOj : #O=j)
    (havoid : Disjoint O d.protectedCols) : d.QuotaFeasible O := by
  refine ⟨hOB,hOj,?_⟩
  intro x hx
  have hz : dg G O x=0 := by
    change #(O.filter (fun z => G.Adj x z))=0
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro z hz hadj
    exact (disjoint_left.mp havoid hz) (d.mem_protected.mpr ⟨x,hx,hadj,hOB hz⟩)
  rw [hz]
  exact Nat.zero_le _

end Data
end Erdos585.AllHThirdTwoQuota
