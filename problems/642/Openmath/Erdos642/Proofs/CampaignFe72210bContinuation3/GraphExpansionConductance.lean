import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.GraphCheegerRayleigh
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Literal cardinal graph expansion implies conductance and connectedness. -/
namespace Erdos642.CampaignFe72210bContinuation3.GraphExpansionConductance
open Matrix Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.FiniteCoarea
open Erdos642.CampaignFe72210bContinuation3.GraphDirichlet
open Erdos642.CampaignFe72210bContinuation3.GraphCheegerRayleigh
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def crossing (S : Finset V) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ Sᶜ, adjWeight G x y

theorem crossing_eq_cut (S : Finset V) : crossing G S = cut (adjWeight G) S := by
  classical
  rw [cut_eq_crossing _ (adjWeight_symmetric G)]
  unfold crossing
  symm
  calc
    _ = ∑ x ∈ S, ∑ y, if x ∈ S ∧ y ∉ S then adjWeight G x y else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      simp [hx]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [hx, true_and]
      rw [← Finset.sum_filter]
      congr 1
      ext y
      simp

theorem cut_compl (S : Finset V) : cut (adjWeight G) Sᶜ = cut (adjWeight G) S := by
  classical
  unfold cut variation
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [indicator, hx, hy]

theorem graph_volume_eq_sum (S : Finset V) :
    volume (adjWeight G) S = ∑ x ∈ S, (G.degree x : ℝ) := by
  classical
  simp only [volume, adjWeight_row]
  rw [← Finset.sum_filter]
  simp

theorem graph_volume_nonneg (S : Finset V) : 0 ≤ volume (adjWeight G) S := by
  rw [graph_volume_eq_sum]
  positivity

theorem smaller_compl {S : Finset V} (hS : ¬ (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (Sᶜ.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
  have hh : S.card + Sᶜ.card = Fintype.card V := by simp
  have hh' : (S.card : ℝ) + (Sᶜ.card : ℝ) = (Fintype.card V : ℝ) := by exact_mod_cast hh
  linarith

section Nonempty
variable [Nonempty V]

omit [DecidableEq V] in
theorem average_degree_ge_min : (G.minDegree : ℝ) ≤ degreeVolume G / (Fintype.card V : ℝ) := by
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset V)) =>
    show (G.minDegree : ℝ) ≤ (G.degree x : ℝ) by exact_mod_cast G.minDegree_le_degree x)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  apply (le_div_iff₀ hN).mpr
  simpa [degreeVolume, mul_comm] using hs

omit [Nonempty V] in
theorem volume_le_ratio_card (K : ℝ)
    (hK : (G.maxDegree : ℝ) ≤ K * (G.minDegree : ℝ)) (S : Finset V) :
    volume (adjWeight G) S ≤ K * (G.minDegree : ℝ) * (S.card : ℝ) := by
  rw [graph_volume_eq_sum]
  calc
    _ ≤ ∑ _x ∈ S, K * (G.minDegree : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      exact (show (G.degree x : ℝ) ≤ (G.maxDegree : ℝ) by exact_mod_cast G.degree_le_maxDegree x).trans hK
    _ = _ := by simp; ring

theorem small_volume_cut (K lam : ℝ) (hK : 1 ≤ K) (hlam : 0 < lam)
    (hratio : (G.maxDegree : ℝ) ≤ K * (G.minDegree : ℝ))
    (hexpand : ∀ S : Finset V, (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 →
      lam * (degreeVolume G / (Fintype.card V : ℝ)) * (S.card : ℝ) ≤ crossing G S)
    (S : Finset V) (hS : (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (lam / K) * volume (adjWeight G) S ≤ cut (adjWeight G) S := by
  have hKpos : 0 < K := by linarith
  calc
    _ ≤ (lam / K) * (K * (G.minDegree : ℝ) * (S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (volume_le_ratio_card G K hratio S) (by positivity)
    _ = lam * (G.minDegree : ℝ) * (S.card : ℝ) := by field_simp
    _ ≤ lam * (degreeVolume G / (Fintype.card V : ℝ)) * (S.card : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (average_degree_ge_min G) hlam.le) (Nat.cast_nonneg _)
    _ ≤ cut (adjWeight G) S := by simpa only [crossing_eq_cut] using hexpand S hS

theorem expansion_conductance (K lam : ℝ) (hK : 1 ≤ K) (hlam : 0 < lam)
    (hratio : (G.maxDegree : ℝ) ≤ K * (G.minDegree : ℝ))
    (hexpand : ∀ S : Finset V, (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 →
      lam * (degreeVolume G / (Fintype.card V : ℝ)) * (S.card : ℝ) ≤ crossing G S)
    (S : Finset V) :
    (lam / K) * volume (adjWeight G) S * volume (adjWeight G) Sᶜ ≤
      degreeVolume G * cut (adjWeight G) S := by
  have hKpos : 0 < K := by linarith
  have hη : 0 ≤ lam / K := by positivity
  have hv := volume_add_compl (adjWeight G) S
  rw [adjWeight_total] at hv
  have hS0 := graph_volume_nonneg G S
  have hSc0 := graph_volume_nonneg G Sᶜ
  by_cases hs : (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2
  · have hh := small_volume_cut G K lam hK hlam hratio hexpand S hs
    have hb := mul_le_mul_of_nonneg_left (show volume (adjWeight G) Sᶜ ≤ degreeVolume G by linarith)
      (mul_nonneg hη hS0)
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ degreeVolume G by linarith)
    nlinarith only [hb, hh']
  · have hh := small_volume_cut G K lam hK hlam hratio hexpand Sᶜ (smaller_compl hs)
    rw [cut_compl] at hh
    have hb := mul_le_mul_of_nonneg_left (show volume (adjWeight G) S ≤ degreeVolume G by linarith)
      (mul_nonneg hη hSc0)
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ degreeVolume G by linarith)
    nlinarith only [hb, hh']

theorem expansion_cut_pos (hdeg : ∀ x : V, 0 < G.degree x) (lam : ℝ) (hlam : 0 < lam)
    (hexpand : ∀ S : Finset V, (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 →
      lam * (degreeVolume G / (Fintype.card V : ℝ)) * (S.card : ℝ) ≤ crossing G S)
    (S : Finset V) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) : 0 < cut (adjWeight G) S := by
  have hW := degreeVolume_positive G hdeg
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  by_cases hs : (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2
  · have hh := hexpand S hs
    rw [crossing_eq_cut] at hh
    have hc : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
    exact lt_of_lt_of_le (by positivity) hh
  · have hh := hexpand Sᶜ (smaller_compl hs)
    rw [crossing_eq_cut, cut_compl] at hh
    have hc : 0 < (Sᶜ.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hSc
    exact lt_of_lt_of_le (by positivity) hh

theorem expansion_connected (hdeg : ∀ x : V, 0 < G.degree x) (lam : ℝ) (hlam : 0 < lam)
    (hexpand : ∀ S : Finset V, (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 →
      lam * (degreeVolume G / (Fintype.card V : ℝ)) * (S.card : ℝ) ≤ crossing G S) :
    G.Connected := by
  classical
  refine { preconnected := ?_ }
  intro x y
  by_contra hxy
  let S := Finset.univ.filter (fun z => G.Reachable x z)
  have hx : x ∈ S := by simp [S]
  have hy : y ∈ Sᶜ := by simp [S, hxy]
  have hp := expansion_cut_pos G hdeg lam hlam hexpand S ⟨x, hx⟩ ⟨y, hy⟩
  have hz : crossing G S = 0 := by
    unfold crossing
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v hv
    have hxu : G.Reachable x u := (Finset.mem_filter.mp hu).2
    have hxv : ¬ G.Reachable x v := by simpa [S] using hv
    have hadj : ¬ G.Adj u v := fun huv => hxv (hxu.trans huv.reachable)
    simp [adjWeight, SimpleGraph.adjMatrix_apply, hadj]
  rw [crossing_eq_cut] at hz
  linarith
end Nonempty
end Erdos642.CampaignFe72210bContinuation3.GraphExpansionConductance
