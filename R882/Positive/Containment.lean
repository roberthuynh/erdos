import R882.Positive.Owners

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
noncomputable section
namespace Erdos585.R882.Positive
open QB4 B5 L34 H3Unequal
open AllHNextNonstrict.TopEscape
open Resources Owners
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace Containment

def Big (q H : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K C P : Finset V) : Prop :=
  ∃ v ∈ residualRows q G A B K C P, (H : ℤ) < -row q G B K v

/-- Actual maximal original sets of cost at most s. -/
structure Owner (q j s : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K P : Finset V) : Prop where
  subset : P ⊆ B\K
  nonempty : P.Nonempty
  cost : extensionCost q j G A B K P ≤ s
  strict : ∀ Q ⊆ B\K, P ⊆ Q → P ≠ Q → (s : ℤ)+1 ≤ extensionCost q j G A B K Q

/-- Nonbig low-cost intersections have fewer than 5h+e original columns. -/
lemma intersection_small {h q j e s : ℕ} {A B K P Q : Finset V}
    (d : Data h q j e G A B) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K=2*(j : ℤ)+s-1) (hs : 1 ≤ s)
    (hP : P ⊆ B\K) (hcP : extensionCost q j G A B K P ≤ s)
    (hQ : Owner q j s G A B K Q) (hn : ¬P ⊆ Q)
    (hminimal : ∀ Z ⊆ B\K, Big q (h+j+s) G A B K (weakCore q G A B K) Z →
      extensionCost q j G A B K P ≤ extensionCost q j G A B K Z) :
    (#(P∩Q) : ℤ) < 5*h+e ∧
      extensionCost q j G A B K (P∩Q) ≤ extensionCost q j G A B K P-1 := by
  classical
  let C := weakCore q G A B K
  let I := P∩Q
  have opt : Optimizer q G A B K C := weak_optimizer q A B K
  have hI : I ⊆ B\K := inter_subset_left.trans hP
  have hneU : Q ≠ P∪Q := by
    intro he
    exact hn (he ▸ subset_union_left)
  have hU := hQ.strict (P∪Q) (union_subset hP hQ.subset) subset_union_right hneU
  have hsub := extensionCost_submod (G:=G) q j A B K P Q
  have hQi := hQ.cost
  have hell : extensionCost q j G A B K I ≤ extensionCost q j G A B K P-1 := by
    dsimp [I];omega
  have hj := d.parameters.j_bounds
  have hshape := high_shape d opt hK hl hp
  have hcount := weak_count d opt hK hl hp
  have hIcard : (#I : ℤ) < 5*h+e := by
    by_cases he : I=∅
    · simp only [he,card_empty,Nat.cast_zero]
      have hh := d.parameters.height_int
      omega
    · have hnb : ¬Big q (h+j+s) G A B K C I := by
        intro hb
        have hh := hminimal I hI hb
        omega
      have hrows : residualRows q G A B K C I ⊆ weakRows q (h+j+s) G A B K C := by
        intro v hv
        apply mem_filter.mpr
        refine ⟨(mem_filter.mp hv).1,?_⟩
        by_contra! ht
        exact hnb ⟨v,hv,ht⟩
      have hrc := card_le_card hrows
      have heta := eta_bounds d opt hK hl hI
        (show extensionCost q j G A B K I < thetaJ q j G A B K by omega)
      dsimp only at hshape
      omega
  exact ⟨hIcard,hell⟩

/-- Every maximal big low-cost owner contains the least-cost big original owner. -/
lemma least_big_contained {h q j e s : ℕ} {A B K P Q : Finset V}
    (d : Data h q j e G A B) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K=2*(j : ℤ)+s-1) (hs : 1 ≤ s)
    (_hmin : ∀ Z ⊆ B\K, Z.Nonempty → 1 ≤ extensionCost q j G A B K Z)
    (hP : P ⊆ B\K) (hcP : extensionCost q j G A B K P ≤ s)
    (hbP : Big q (h+j+s) G A B K (weakCore q G A B K) P)
    (hminimal : ∀ Z ⊆ B\K, Big q (h+j+s) G A B K (weakCore q G A B K) Z →
      extensionCost q j G A B K P ≤ extensionCost q j G A B K Z)
    (hQ : Owner q j s G A B K Q)
    (hbQ : Big q (h+j+s) G A B K (weakCore q G A B K) Q) : P ⊆ Q := by
  classical
  by_contra hn
  let C := weakCore q G A B K
  let JP := residualRows q G A B K C P
  let JQ := residualRows q G A B K C Q
  let Y := JP∩JQ
  let I := P∩Q
  have opt : Optimizer q G A B K C := weak_optimizer q A B K
  have hsmall := intersection_small d hK hl hp hs hP hcP hQ hn hminimal
  have hcp := big_columns_large d opt hK hl hp hP hcP hbP
  have hcq := big_columns_large d opt hK hl hp hQ.subset hQ.cost hbQ
  have hIP : I ⊆ P := inter_subset_left
  have hIQ : I ⊆ Q := inter_subset_right
  have hcip := card_sdiff_add_card_eq_card hIP
  have hciq := card_sdiff_add_card_eq_card hIQ
  have hnum := d.parameters.owner_numeric
  have hguardP : h ≤ #(P\I) := by dsimp only [I] at hcip ⊢; omega
  have hguardQ : h ≤ #(Q\I) := by dsimp only [I] at hciq ⊢; omega
  have hpcharge := exclusive_charge d opt hK hl hP hIP hguardP
    (inter_subset_left : Y ⊆ residualRows q G A B K C P)
  have hqcharge := exclusive_charge d opt hK hl hQ.subset hIQ hguardQ
    (inter_subset_right : Y ⊆ residualRows q G A B K C Q)
  have hpool := Owners.pair_pool (C:=C) d hP hQ.subset
  have hrefund := repeated_refund (G:=G) (q:=q) (Y:=Y) hK hP hQ.subset
  have hbudget := PetalEscape.pool_bound d opt hK
  have hcap := four_row_cap (JP:=JP) (JQ:=JQ) d opt.subset
    (filter_subset _ _ : JP ⊆ A\C) (filter_subset _ _ : JQ ⊆ A\C)
    ((inter_subset_left.trans hP).trans sdiff_subset : I ⊆ B)
  have hetaP := eta_bounds d opt hK hl hP
    (show extensionCost q j G A B K P < thetaJ q j G A B K by
      have hj:=d.parameters.j_pos;omega)
  have hetaQ := eta_bounds d opt hK hl hQ.subset
    (show extensionCost q j G A B K Q < thetaJ q j G A B K by
      have hj:=d.parameters.j_pos;have hc:=hQ.cost;omega)
  have hqc := hQ.cost
  have hh := d.parameters.height_int
  have hj := d.parameters.j_bounds
  have hn := d.parameters.numeric
  have ha := d.parameters.offset_cast
  have he := d.parameters.error_int
  have hprod := mul_nonneg (show 0≤(h : ℤ)-j-1 by omega)
    (Nat.cast_nonneg q : (0 : ℤ)≤q)
  dsimp only at hpool
  dsimp only [Y,I,JP,JQ] at *
  have hpaid : ((h : ℤ)-j)*q-offset h e-2*e+3*j-2*h+2 ≤ 0 := by
    linarith only [hpcharge,hqcharge,hpool,hrefund,hbudget,hcap,
      hetaP.1,hetaQ.1,hcP,hqc,hp]
  nlinarith only [hpaid,hprod,hnum.2.2.1,ha,he,hj.1]

end Containment
end Erdos585.R882.Positive
