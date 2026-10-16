import R863.PetalEscape
import AllHNextNonstrict.TopEscape

/-! R257 original-resource machinery adapted to the full-error R851 height band. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
noncomputable section
namespace Erdos585.R863
open QB4 B5 L34 H3Unequal
open AllHNextNonstrict.TopEscape
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace Resources

/-- The changed imbalance and original outside scar remain coupled. -/
lemma high_shape {h q j e s : ℕ} {A B K C : Finset V}
    (d : Data h q j e G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K = 2*(j : ℤ)+s-1) :
    let k : ℤ := (#C : ℤ)-#K
    let z : ℤ := k-j-s+e
    1 ≤ (h : ℤ)-k ∧ 0 ≤ z ∧
      z = coreDefect q G C K-((h : ℤ)*q-offset h e-e+1)+
        deficiency (2*(q : ℤ)-2) G B (A\C) := by
  classical
  have hj := d.parameters.j_pos
  have hs := d.positive_shape opt hK hl (by omega)
  have hn := d.scar_nonneg (sdiff_subset : A\C ⊆ A)
  dsimp only at hs ⊢
  omega

/-- Actual incoming original edges and scars have this exact joint bound. -/
lemma incoming_bound {h q j e : ℕ} {A B K C : Finset V}
    (d : Data h q j e G A B) (opt : Optimizer q G A B K C) (hK : K ⊆ B) :
    (ec G (A\C) K : ℤ)+deficiency (2*(q : ℤ)-2) G B (A\C) ≤
      ((h : ℤ)-((#C : ℤ)-#K))*q+j+2*((#C : ℤ)-#K)-
        thetaJ q j G A B K-offset h e := by
  classical
  have hi := opt.cross_scar_identity (j:=j)
  have hs := d.scar_split opt.subset
  have hb : 0 ≤ deficiency (2*(q : ℤ)-2) G A K :=
    deficiency_nonneg _ fun v hv => d.capB_int (hK hv)
  nlinarith

def weakRows (q H : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K C : Finset V) : Finset V :=
  (A\C).filter fun v => -row q G B K v ≤ H

/-- Every weak original row consumes its incoming edges PLUS its full scar. -/
lemma weak_charge {q H : ℕ} {A B K C : Finset V} :
    ((q : ℤ)-2-H)*#(weakRows q H G A B K C) ≤
      (ec G (weakRows q H G A B K C) K : ℤ)+
        deficiency (2*(q : ℤ)-2) G B (weakRows q H G A B K C) := by
  classical
  rw [ec,Nat.cast_sum,deficiency,←sum_add_distrib]
  calc
    _ = ∑ _v ∈ weakRows q H G A B K C, ((q : ℤ)-2-H) := by
      rw [sum_const,nsmul_eq_mul];ring
    _ ≤ _ := by
      apply sum_le_sum
      intro v hv
      have hh := (mem_filter.mp hv).2
      unfold row at hh
      omega

/-- Weak original rows spend at least half q units of the incoming pool. -/
lemma weak_count {h q j e s : ℕ} {A B K C : Finset V}
    (d : Data h q j e G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K = 2*(j : ℤ)+s-1) :
    (#(weakRows q (h+j+s) G A B K C) : ℤ) < 4*h := by
  classical
  have hs := high_shape d opt hK hl hp
  let W := weakRows q (h+j+s) G A B K C
  have hW : W ⊆ A\C := filter_subset _ _
  have hch := weak_charge (G:=G) (q:=q) (H:=h+j+s) (A:=A) (B:=B) (K:=K) (C:=C)
  have he : ec G W K ≤ ec G (A\C) K := by
    rw [ec_comm (G:=G) W K,ec_comm (G:=G) (A\C) K]
    exact ec_mono_right (G:=G) K hW
  have hscar := deficiency_le_subset (2*(q : ℤ)-2) hW
    (fun v hv => d.capA_int (mem_sdiff.mp hv).1)
  have hbudget := PetalEscape.pool_bound d opt hK
  have hh := d.parameters.height_int
  have hj := d.parameters.j_bounds
  have hn := d.parameters.numeric
  have hnum := d.parameters.owner_numeric
  have hout : (0 : ℤ) ≤ ec G C (B\K) := Nat.cast_nonneg _
  dsimp only at hs
  have hH : (h : ℤ)+j+s ≤ 2*h+e-1 := by omega
  have hhalf : (q : ℤ) ≤ 2*((q : ℤ)-2-(h+j+s)) := by omega
  have hgap := mul_nonneg (show 0≤(h : ℤ)-j-1 by omega)
    (Nat.cast_nonneg q : (0 : ℤ)≤q)
  have hpool : (ec G (A\C) K : ℤ)+deficiency (2*(q : ℤ)-2) G B (A\C) <
      2*(h : ℤ)*q := by nlinarith
  zify at he
  change ((q : ℤ)-2-(h+j+s))*#W ≤ _ at hch
  have hu0 : (0 : ℤ) ≤ #W := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right hhalf hu0
  have hq := d.parameters.q_pos
  change (#W : ℤ) < 4*h
  nlinarith

/-- Every actual expansion below the current height has the literal imbalance bounds. -/
lemma eta_bounds {h q j e : ℕ} {A B K C P : Finset V}
    (d : Data h q j e G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K) (hP : P ⊆ B\K)
    (hc : extensionCost q j G A B K P < thetaJ q j G A B K) :
    ((#C : ℤ)-#K)-(h : ℤ)+1 ≤ (#P : ℤ)-#(residualRows q G A B K C P) ∧
      (#P : ℤ)-#(residualRows q G A B K C P) ≤
        j+((#C : ℤ)-#K)-thetaJ q j G A B K-1+extensionCost q j G A B K P+e := by
  classical
  let J := residualRows q G A B K C P
  have hJ : J ⊆ A\C := filter_subset _ _
  have hdC : Disjoint C J := disjoint_left.mpr fun v hv hj => (mem_sdiff.mp (hJ hj)).2 hv
  have hdK : Disjoint K P := disjoint_left.mpr fun v hv hp => (mem_sdiff.mp (hP hp)).2 hv
  have hxp : 0 < thetaJ q j G A B (K∪P) := by unfold extensionCost at hc;omega
  have hs := d.positive_shape (expanded_optimizer opt hP)
    (union_subset hK (hP.trans sdiff_subset)) (hl.trans (card_le_card subset_union_left)) hxp
  have hcc := card_union_of_disjoint hdC
  have hcp := card_union_of_disjoint hdK
  have hn := d.scar_nonneg (sdiff_subset : A\(C∪J) ⊆ A)
  dsimp only at hs
  change _ ≤ (#P : ℤ)-#J ∧ (#P : ℤ)-#J ≤ _
  zify at hcc hcp
  unfold extensionCost
  dsimp only [J] at hcc hcp hn ⊢
  omega

/-- Original singleton positivity bounds outgoing edges on every repeated column. -/
lemma repeated_outgoing {q j : ℕ} {A B K C P : Finset V}
    (opt : Optimizer q G A B K C)
    (hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hP : P ⊆ B\K) : (ec G C P : ℤ) ≤ ((q : ℤ)-1)*#P := by
  classical
  rw [ec_comm,ec,Nat.cast_sum]
  calc
    _ ≤ ∑ _v∈P, ((q : ℤ)-1) := by
      apply sum_le_sum
      intro v hv
      have hh := singleton_weight_pos opt hmin (hP hv)
      omega
    _ = _ := by rw [sum_const,nsmul_eq_mul];ring

end Resources
end Erdos585.R863
