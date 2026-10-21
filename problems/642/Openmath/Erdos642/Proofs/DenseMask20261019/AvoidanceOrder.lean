import Openmath.Erdos642.Proofs.Joint20261019.Original
import Openmath.Erdos642.Proofs.DenseMask20261019.ComponentObstruction

/-! The protected whole-original theorem supplies the actual component-order bound. -/
namespace Erdos642.DenseMask20261019.AvoidanceOrder

open SimpleGraph Finset
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3
open Erdos642.CampaignFe72210bContinuation3.CutExtraction

universe u

noncomputable def orderLower (C q : ℝ) : ℝ :=
  (1/2) * Real.exp ((q / (2*C)) ^ (4 : ℝ)⁻¹)

/-- Handshaking and power inversion, for an actual nonempty original graph. -/
theorem order_lower_of_density {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (C q : ℝ) (hC : 0 < C) (hq : 0 ≤ q)
    (hdegree : ∀ x, q ≤ (G.degree x : ℝ))
    (hedges : (G.edgeFinset.card : ℝ) ≤
      C * Erdos642.Joint20261019.AllOrders.psi (Fintype.card V)) :
    orderLower C q ≤ (Fintype.card V : ℝ) := by
  classical
  let n := Fintype.card V
  have hnN : 0 < n := Fintype.card_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast hnN
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog : 0 < Real.log (2*(n : ℝ)) := Real.log_pos (by linarith)
  have hsum : q * (n : ℝ) ≤ 2*(G.edgeFinset.card : ℝ) := by
    have hs : (∑ x : V, q) ≤ ∑ x : V, (G.degree x : ℝ) :=
      Finset.sum_le_sum (fun x _ => hdegree x)
    have he : (∑ x : V, (G.degree x : ℝ)) = 2*(G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    simpa [n, mul_comm] using hs.trans_eq he
  have hedge : (G.edgeFinset.card : ℝ) ≤ C*(n : ℝ)*Real.log (2*(n : ℝ))^4 := by
    simpa only [Erdos642.Joint20261019.AllOrders.psi, n, mul_assoc] using hedges
  have hqlog : q ≤ 2*C*Real.log (2*(n : ℝ))^4 := by
    have hh : q*(n : ℝ) ≤ (2*C*Real.log (2*(n : ℝ))^4)*(n : ℝ) := by
      nlinarith [hedge]
    exact (mul_le_mul_iff_left₀ hn).mp hh
  have hbase : q/(2*C) ≤ Real.log (2*(n : ℝ))^4 :=
    (div_le_iff₀ (by positivity : 0 < 2*C)).mpr (by nlinarith [hqlog])
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ q/(2*C)) hbase
    (by positivity : 0 ≤ (4 : ℝ)⁻¹)
  have hroot : (q/(2*C)) ^ (4 : ℝ)⁻¹ ≤ Real.log (2*(n : ℝ)) := by
    have heq : (Real.log (2*(n : ℝ))^4) ^ (4 : ℝ)⁻¹ = Real.log (2*(n : ℝ)) := by
      convert Real.pow_rpow_inv_natCast hlog.le (by decide : (4 : ℕ) ≠ 0) using 1 <;>
        norm_num
    rwa [heq] at hr
  have he := Real.exp_le_exp.mpr hroot
  rw [Real.exp_log (by positivity : 0 < 2*(n : ℝ))] at he
  unfold orderLower
  change (1/2 : ℝ) * Real.exp ((q/(2*C)) ^ (4 : ℝ)⁻¹) ≤ (n : ℝ)
  linarith

/- A single absolute constant from the protected whole-original theorem
works for every actual induced set of every rich-cycle-avoiding graph. -/
attribute [-instance] FinsetCoe.fintype in
theorem exists_induced_order_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
        ∀ (S : Finset V), S.Nonempty → ∀ q : ℝ, 0 ≤ q →
          (∀ x ∈ S, q ≤ (restrictedDegree G S x : ℝ)) →
          orderLower C q ≤ (S.card : ℝ) := by
  classical
  obtain ⟨C, hC, hwhole⟩ := Erdos642.Joint20261019.Original.original_joint_rich_cycle.{u}
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ havoid S hS q hq hdegree
  let H := G.induce (S : Set V)
  letI : Nonempty (S : Set V) := hS.to_subtype
  have hcard : Fintype.card (S : Set V) = S.card :=
    Fintype.card_of_finset' S (fun _ => Iff.rfl)
  let f : H →g G := { toFun := Subtype.val, map_rel' := fun h => h }
  have havoidH : ¬HasRichCycle H :=
    not_hasRichCycle_of_injective_hom f Subtype.val_injective havoid
  have hedges : (H.edgeFinset.card : ℝ) ≤
      C * Erdos642.Joint20261019.AllOrders.psi (Fintype.card (S : Set V)) := by
    apply le_of_not_gt
    intro hdense
    exact havoidH (hwhole (S : Set V) H hdense)
  have hmin : ∀ x : (S : Set V), q ≤ (H.degree x : ℝ) := by
    intro x
    rw [← restrictedDegree_eq_induce G S x]
    exact hdegree x.val x.property
  simpa only [hcard] using order_lower_of_density H C q hC hq hmin hedges

/-- The order supplier consumed by the actual component witness, with
rich-cycle avoidance rather than an assumed minimum-degree-to-order bound. -/
theorem exists_component_order_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
        ∀ (Q : Finset V) (q : ℝ), 0 ≤ q →
          (∀ x ∈ Q, q ≤ (restrictedDegree G Q x : ℝ)) →
          ∀ c : (mask G Q).ConnectedComponent,
            (∃ x ∈ Q, x ∈ c.supp) →
            orderLower C q ≤ ((ComponentObstruction.componentVertices G Q c).card : ℝ) := by
  obtain ⟨C, hC, horder⟩ := exists_induced_order_constant.{u}
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ havoid Q q hq hdegree c hc
  exact ComponentObstruction.component_order_lower G Q q (orderLower C q) hdegree
    (fun S hS hmin => horder V G havoid S hS q hq hmin) c hc

end Erdos642.DenseMask20261019.AvoidanceOrder
