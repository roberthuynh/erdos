import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.LocalCodegreeSubgraph

/-! Authentic global P8 avoidance derives an actual local fourth-return bound. -/
namespace Erdos642.CampaignFe72210bContinuation3.LocalAvoidanceMoment
open Erdos642.CampaignFe72210b
open FourthReturnExpansion LocalCodegreeIncidence LocalCodegreeSubgraph
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- External published P8 input with its actual all-graph avoidance scope. -/
def AllAvoidingP8 (C : ℝ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj], ¬ HasRichCycle H →
    (H.edgeFinset.card : ℝ) ≤ C*(Fintype.card W : ℝ)*Real.log (2*(Fintype.card W : ℝ))^8

noncomputable def coefficient (C : ℝ) (Δ : ℕ) : ℝ :=
  1+C*Real.log (2*((Δ : ℝ)+(Δ : ℝ)^2))^8

theorem coefficient_ge_one (C : ℝ) (hC : 0 ≤ C) (Δ : ℕ) : 1 ≤ coefficient C Δ := by
  unfold coefficient
  have hh : 0 ≤ C*Real.log (2*((Δ : ℝ)+(Δ : ℝ)^2))^8 := by positivity
  linarith

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem threshold_density (C : ℝ) (hC : 0 ≤ C) (hP8 : AllAvoidingP8.{u} C)
    (havoid : ¬ HasRichCycle G) (hbip : G.IsBipartite) (Δ : ℕ) (_hΔ : 1 ≤ Δ)
    (hmax : ∀ x, G.degree x ≤ Δ) (v : V) (hv : 0 < G.degree v)
    (j : ℕ) (hj : 1 ≤ j) :
    (j : ℝ)*((layer G v j).card : ℝ) ≤
      coefficient C Δ*((G.degree v : ℝ)+((layer G v j).card : ℝ)) := by
  classical
  have hdensity := threshold_density_from_P8 G C hP8 havoid hbip v j hj
  have horder := incidence_order_le G v j hj Δ hmax
  rw [incidence_order] at horder
  have horder' : (G.degree v : ℝ)+((layer G v j).card : ℝ) ≤
      (Δ : ℝ)+(Δ : ℝ)^2 := by exact_mod_cast horder
  have hv' : (1 : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast (show 1 ≤ G.degree v from hv)
  have hn : (1 : ℝ) ≤ (G.degree v : ℝ)+((layer G v j).card : ℝ) := by
    have hh : (0 : ℝ) ≤ (layer G v j).card := Nat.cast_nonneg _
    linarith
  have hlog0 : 0 ≤ Real.log (2*((G.degree v : ℝ)+((layer G v j).card : ℝ))) :=
    Real.log_nonneg (by linarith)
  have hlog := Real.log_le_log
    (show 0 < 2*((G.degree v : ℝ)+((layer G v j).card : ℝ)) by positivity)
    (show 2*((G.degree v : ℝ)+((layer G v j).card : ℝ)) ≤ 2*((Δ : ℝ)+(Δ : ℝ)^2) by linarith)
  have hpow := pow_le_pow_left₀ hlog0 hlog 8
  have hinc : (j : ℝ)*((layer G v j).card : ℝ) ≤
      ∑ w ∈ layer G v j, (codegree G v w : ℝ) := by
    calc
      _ = ∑ _w ∈ layer G v j, (j : ℝ) := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro w hw
        exact_mod_cast (Finset.mem_filter.mp hw).2
  apply hinc.trans (hdensity.trans _)
  have hm := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ C*((G.degree v : ℝ)+((layer G v j).card : ℝ)) by positivity)
  have hn0 : 0 ≤ (G.degree v : ℝ)+((layer G v j).card : ℝ) := by positivity
  unfold coefficient
  nlinarith only [hm,hn0]

theorem codegree_square_sum (C : ℝ) (hC : 0 ≤ C) (hP8 : AllAvoidingP8.{u} C)
    (havoid : ¬ HasRichCycle G) (hbip : G.IsBipartite) (Δ : ℕ) (hΔ : 1 ≤ Δ)
    (hmax : ∀ x, G.degree x ≤ Δ) (v : V) (hv : 0 < G.degree v) :
    (∑ w ∈ Finset.univ.erase v, (Fintype.card (G.commonNeighbors v w) : ℝ)^2) ≤
      8*coefficient C Δ*(Δ : ℝ)^2 := by
  have hc : ∀ w ∈ Finset.univ.erase v, codegree G v w ≤ Δ := by
    intro w _
    exact (G.card_commonNeighbors_le_degree_left v w).trans (hmax v)
  have hm : CodegreeLayerCake.mass (Finset.univ.erase v) (codegree G v) ≤
      (G.degree v : ℝ)*(Δ : ℝ) := offdiag_common_mass_le G v Δ hmax
  have hd : ∀ j ∈ Finset.Icc 1 Δ,
      (j : ℝ)*((CodegreeLayerCake.threshold (Finset.univ.erase v) (codegree G v) j).card : ℝ) ≤
      coefficient C Δ*((G.degree v : ℝ)+
        ((CodegreeLayerCake.threshold (Finset.univ.erase v) (codegree G v) j).card : ℝ)) := by
    intro j hj
    exact threshold_density G C hC hP8 havoid hbip Δ hΔ hmax v hv j (Finset.mem_Icc.mp hj).1
  have hs := CodegreeLayerCake.square_sum_le_eight (Finset.univ.erase v) (codegree G v) Δ
    (coefficient C Δ) (G.degree v : ℝ) (coefficient_ge_one C hC Δ)
    (Nat.cast_nonneg _) hc hm hd
  apply hs.trans
  have hdeg : (G.degree v : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hmax v
  have ha : 0 ≤ 8*coefficient C Δ*(Δ : ℝ) := by
    have hh := coefficient_ge_one C hC Δ
    positivity
  have hh := mul_le_mul_of_nonneg_left hdeg ha
  nlinarith only [hh]

/-- Genuine uniform fourth return from avoidance and authentic external P8 only. -/
theorem graph_fourth_return_from_P8 (C : ℝ) (hC : 0 ≤ C) (hP8 : AllAvoidingP8.{u} C)
    (havoid : ¬ HasRichCycle G) (hbip : G.IsBipartite) (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ)) (Δ : ℕ) (hΔ : 1 ≤ Δ)
    (hmax : ∀ x : V, G.degree x ≤ Δ) (v : V) :
    (graphTransition G ^ 4) v v ≤ 1/d^2+8*coefficient C Δ*(Δ : ℝ)^2/d^4 := by
  have hv : 0 < G.degree v := by exact_mod_cast hd.trans_le (hmin v)
  have hs := codegree_square_sum G C hC hP8 havoid hbip Δ hΔ hmax v hv
  apply (graphTransition_fourth_return_le_codegree G d hd hmin v).trans
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hs (show (0 : ℝ) ≤ d^4 by positivity))
end Erdos642.CampaignFe72210bContinuation3.LocalAvoidanceMoment
