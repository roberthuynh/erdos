import Openmath.AllHTopCritical.Original

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.AllHTopCritical
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}
variable {h q : ℕ} {A B R T : Finset V}

namespace TopCore
variable (host : Host h q G A B) (core : TopCore h q G A B R T)
include host core

lemma reverse_imbalance : #(B\T) = #(A\R)+(h-1) := by
  have hr := card_sdiff_add_card_eq_card core.subset
  have ht := card_sdiff_add_card_eq_card core.T_subset
  have hb := host.balanced
  have hi := core.imbalance
  omega

lemma outside_zero : deficiency (2*(q : ℤ)-2) G B (A\R) = 0 := by
  have hs := sum_sdiff core.subset (f := fun v => 2*(q : ℤ)-2-(dg G B v : ℤ))
  change deficiency (2*(q : ℤ)-2) G B (A\R) +
      deficiency (2*(q : ℤ)-2) G B R = deficiency (2*(q : ℤ)-2) G B A at hs
  rw [host.deficiency_A, core.captured] at hs
  omega

lemma outside_saturated : ∀ v ∈ A\R, G.degree v = 2*q-2 := by
  intro v hv
  have hq := host.parameters.q_pos
  have hz : deficiency ((2*q-2 : ℕ) : ℤ) G B (A\R) = 0 := by
    have hc : ((2*q-2 : ℕ) : ℤ) = 2*(q : ℤ)-2 := by omega
    rw [hc]
    exact core.outside_zero host
  have he := saturated_of_zero
    (fun x hx => host.capA x (sdiff_subset hx)) hz hv
  rw [dg_eq_degree host.bipartite (sdiff_subset hv)] at he
  exact he

lemma cross_and_scar :
    (ec G (A\R) T : ℤ) + deficiency (2*(q : ℤ)-2) G A T =
      (q : ℤ)+h-offset h := by
  have he := core.optimizer.cross_scar_identity (j := 0)
  rw [core.height, core.captured] at he
  have hc := host.parameters.constant_cast
  have hs := host.parameters.surplus_cast
  have hi := core.imbalance
  zify at hi
  norm_num at he
  nlinarith

lemma cross_le : (ec G (A\R) T : ℤ) ≤ (q : ℤ)+h-offset h := by
  have he := core.cross_and_scar host
  have hn := deficiency_nonneg (G := G) (2*(q : ℤ)-2)
    (fun v hv => host.capB_int v (core.T_subset hv))
  linarith

lemma internal_first : (ec G R T : ℤ) =
    (2*(q : ℤ)-2)*#T-((q : ℤ)+h-offset h) := by
  have hf := core.first_deficit
  have hc := host.parameters.constant_cast
  have hs := host.parameters.surplus_cast
  have hi := core.imbalance
  zify at hi
  unfold coreDefect at hf
  nlinarith

lemma outside_total : (ec G (A\R) B : ℤ) = (2*(q : ℤ)-2)*#(A\R) := by
  have hz := core.outside_zero host
  rw [deficiency_eq] at hz
  omega

lemma T_pos : 1 ≤ #T := by
  have hi := core.imbalance
  have hl := core.eligible
  have hq := host.parameters.q_ge
  omega

lemma outside_pos : 1 ≤ #(A\R) := by
  by_contra hn
  have hz : A\R = ∅ := card_eq_zero.mp (by omega)
  have he := ec_sdiff_add_left (G := G) core.subset (B\T)
  rw [hz] at he
  simp only [ec, sum_empty, zero_add] at he
  change ec G R (B\T) = ec G A (B\T) at he
  have hm := Bq.ec_lower_of_min (G := G) (sdiff_subset : B\T ⊆ B) host.minB
  rw [ec_comm (G := G) (B\T) A, ← he] at hm
  have hf := core.forward host.parameters
  have hi := core.reverse_imbalance host
  have hs := host.parameters.surplus_cast
  have hh := host.parameters.height_int
  rw [hz, card_empty] at hi
  zify at hm hi
  nlinarith

lemma T_large : 2*q-h-1 ≤ #T := by
  apply host.parameters.quadratic_order (core.T_pos host)
  have he := core.internal_first host
  have hs := host.parameters.surplus_cast
  have hi := core.imbalance
  have hu := ec_le_product (G := G) R T
  zify at hi hu
  nlinarith

lemma outside_large : 2*q-h-1 ≤ #(A\R) := by
  apply host.parameters.quadratic_order (core.outside_pos host)
  have ht := core.outside_total host
  have hs := ec_sdiff_add_right (G := G) core.T_subset (A\R)
  have hc := core.cross_le host
  have hi := core.reverse_imbalance host
  have hcast := host.parameters.surplus_cast
  have hu := ec_le_product (G := G) (A\R) (B\T)
  zify at hs hi hu
  nlinarith

lemma complement_eligible : 2*q ≤ #(A\R)+#(B\T) := by
  have hv := core.outside_large host
  have hi := core.reverse_imbalance host
  have hn := host.parameters.numeric
  have hh := host.parameters.height
  omega

lemma complement_proper : #(A\R)+#(B\T) < Fintype.card V := by
  have hr := card_sdiff_add_card_eq_card core.subset
  have ht := card_sdiff_add_card_eq_card core.T_subset
  have ho := host.shore_order
  have hp := core.T_pos host
  omega

lemma second_identity : coreDefect q G (A\R) (B\T) =
    ((q : ℤ)-1)*((h : ℤ)-1)+(ec G (A\R) T : ℤ) := by
  have ht := core.outside_total host
  have he := ec_sdiff_add_right (G := G) core.T_subset (A\R)
  have hi := core.reverse_imbalance host
  have hs := host.parameters.surplus_cast
  zify at he hi
  unfold coreDefect
  nlinarith

lemma cross_exact : (ec G (A\R) T : ℤ) = (q : ℤ)+h-offset h := by
  have hf := host.paired_floor (sdiff_subset : A\R ⊆ A)
    (sdiff_subset : B\T ⊆ B) (core.complement_eligible host) (core.complement_proper host)
  have he := core.second_identity host
  have hc := host.parameters.constant_cast
  have hu := core.cross_le host
  nlinarith

lemma T_saturated : ∀ v ∈ T, G.degree v = 2*q-2 := by
  have hq := host.parameters.q_pos
  have he := core.cross_and_scar host
  rw [core.cross_exact host] at he
  have hz : deficiency ((2*q-2 : ℕ) : ℤ) G A T = 0 := by
    have hc : ((2*q-2 : ℕ) : ℤ) = 2*(q : ℤ)-2 := by omega
    rw [hc]
    omega
  intro v hv
  have hd := saturated_of_zero (fun x hx => host.capB x (core.T_subset hx)) hz hv
  rw [dg_eq_degree host.bipartite.symm (core.T_subset hv)] at hd
  exact hd

lemma second_deficit : coreDefect q G (A\R) (B\T) = (constant h q : ℤ)+1 := by
  rw [core.second_identity host, core.cross_exact host, host.parameters.constant_cast]
  ring

lemma total_large : 8*q-2*h-6 ≤ Fintype.card V := by
  have ht := core.T_large host
  have hv := core.outside_large host
  have hi := core.imbalance
  have hc := card_sdiff_add_card_eq_card core.subset
  have ho := host.shore_order
  have hb := host.balanced
  have hn := host.parameters.numeric
  have hh := host.parameters.height
  omega

theorem rigidity : Rigidity h q G A B R T := by
  exact ⟨core.T_saturated host, core.outside_saturated host, core.reverse_imbalance host,
    core.forward host.parameters, core.cross_exact host, core.first_deficit,
    core.second_deficit host, core.T_large host, core.outside_large host, core.total_large host⟩

end TopCore
end Erdos585.AllHTopCritical
