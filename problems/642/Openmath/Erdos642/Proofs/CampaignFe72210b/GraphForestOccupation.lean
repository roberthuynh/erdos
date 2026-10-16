import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphForestFirstStage
import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestSecondStage

/-! Actual graph two-window forest occupation, before numeric absorption or SA. -/
namespace Erdos642.CampaignFe72210b.ForestBundle
open Erdos642.FiniteMarkov Erdos642.OccupationTail
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A B : Finset V} {q m b : ℕ}
variable (F : Erdos642.CampaignFe72210b.ForestBundle G A B q m b)

omit [Fintype V] in
/-- Literal good and bad stars partition each finite forest. -/
theorem goodInForest_card_add_badInForest_card (f : Fin q) (leafcut : ℝ)
    {n : ℕ} (x : V) (p : Path V n) :
    (F.goodInForest f leafcut x p).card + (F.badInForest f leafcut x p).card = m := by
  classical
  simpa only [goodInForest, badInForest, not_le, Finset.card_univ, Fintype.card_fin] using
    (Finset.univ : Finset (Fin m)).card_filter_add_card_filter_not
      (fun j => leafcut ≤ occupation (F.leaves (f, j)) x p)

/-- The success predicate depends only on the completed first interval. -/
def firstStageSuccess (leafcut : ℝ) {n : ℕ} (x : V) (p : Path V n) : Prop :=
  ¬ ∃ f : Fin q, (m + 1) / 2 ≤ (F.badInForest f leafcut x p).card

omit [Fintype V] in
/-- Exact integer good-root cardinality, including odd m and dense m=1. -/
theorem firstStageSuccess_goodRootSet_card (leafcut : ℝ) {n : ℕ}
    (x : V) (p : Path V n) (hp : F.firstStageSuccess leafcut x p) :
    q * ((m + 1) / 2) ≤ (F.goodRootSet leafcut x p).card := by
  have hf : ∀ f : Fin q, (m + 1) / 2 ≤ (F.goodInForest f leafcut x p).card := by
    intro f
    have hb : (F.badInForest f leafcut x p).card < (m + 1) / 2 :=
      Nat.lt_of_not_ge (fun hh => hp ⟨f, hh⟩)
    have hpart := F.goodInForest_card_add_badInForest_card f leafcut x p
    omega
  rw [F.goodRootSet_card]
  calc
    q * ((m + 1) / 2) = ∑ _f : Fin q, (m + 1) / 2 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun f _ => hf f)

variable [DecidableRel G.Adj]

/-- Both actual graph occupation stages, with exact finite forest constants. -/
theorem graph_two_window_low_weightedCount_eventMass_le
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hdeg : ∀ x : V, 0 < G.degree x) (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d)
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (hb : 1 ≤ b) (hm : 1 ≤ m) (t : ℕ) (ht : 2 ≤ t) (g : ℕ) (x : V) :
    (graphChain G hdeg).eventMass (((t - 1) + g) + (t - 1))
      (fun _ w => F.windowWeightedCount (graphChain G hdeg) (t - 1) g (t - 1) x w <
        ((t : ℝ) * (b : ℝ) / (600 * (Fintype.card V : ℝ))) *
          ((t : ℝ) * ((q * ((m + 1) / 2) : ℕ) : ℝ) / (300 * (Fintype.card V : ℝ)))) x ≤
      (q : ℝ) * ((2 : ℝ)^m * (200 * (Fintype.card V : ℝ)) * Real.exp
        (-γ * (t : ℝ) * ((((m + 1) / 2) * b : ℕ) : ℝ) / (10000 * (Fintype.card V : ℝ)))) +
      (200 * (Fintype.card V : ℝ)) * Real.exp
        (-γ * (t : ℝ) * ((q * ((m + 1) / 2) : ℕ) : ℝ) / (10000 * (Fintype.card V : ℝ))) := by
  classical
  have : Nonempty V := ⟨x⟩
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  let leafcut : ℝ := (t : ℝ) * (b : ℝ) / (600 * (Fintype.card V : ℝ))
  let u : ℕ := q * ((m + 1) / 2)
  let delta : ℝ := (200 * (Fintype.card V : ℝ)) * Real.exp
    (-γ * (t : ℝ) * (u : ℝ) / (10000 * (Fintype.card V : ℝ)))
  let epsilon : ℝ := (q : ℝ) * ((2 : ℝ)^m * (200 * (Fintype.card V : ℝ)) * Real.exp
    (-γ * (t : ℝ) * ((((m + 1) / 2) * b : ℕ) : ℝ) / (10000 * (Fintype.card V : ℝ))))
  have hfirst : (graphChain G hdeg).eventMass (t - 1)
      (fun _ p => ¬ F.firstStageSuccess leafcut x p) x ≤ epsilon := by
    have hh := F.graph_any_bad_forest_eventMass_le hbi hdeg d hd hmin hmax γ hgap hb hm t ht x
    have he : (graphChain G hdeg).eventMass (t - 1)
        (fun _ p => ¬ F.firstStageSuccess leafcut x p) x =
        (graphChain G hdeg).eventMass (t - 1)
          (fun y p => ∃ f : Fin q, (m + 1) / 2 ≤ (F.badInForest f leafcut y p).card) x := by
      unfold Chain.eventMass
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : ∃ f : Fin q, (m + 1) / 2 ≤ (F.badInForest f leafcut x p).card
      · simp [firstStageSuccess, hp]
      · simp [firstStageSuccess, hp]
    rw [he]
    exact hh
  have hfixed : ∀ U : Finset V, U ⊆ A → u ≤ U.card → ∀ y : V,
      (graphChain G hdeg).eventMass (t - 1) (fun z r => occupation U z r <
        (t : ℝ) * (U.card : ℝ) / (300 * (Fintype.card V : ℝ))) y ≤ delta := by
    intro U hU hcard y
    have hh := graph_occupation_tail_finset G B A hbi.symm hdeg d hd hmin hmax γ hgap U hU t ht y
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hc : (u : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hcard
    have hmul : γ * (t : ℝ) * (u : ℝ) ≤ γ * (t : ℝ) * (U.card : ℝ) :=
      mul_le_mul_of_nonneg_left hc (mul_nonneg hgap.1.le (Nat.cast_nonneg t))
    have hdiv := div_le_div_of_nonneg_right hmul
      (by positivity : 0 ≤ 10000 * (Fintype.card V : ℝ))
    simpa only [neg_mul, neg_div] using neg_le_neg hdiv
  exact F.low_windowWeightedCount_eventMass_le (graphChain G hdeg) (t - 1) g t
    leafcut (Fintype.card V : ℝ) delta epsilon (by dsimp [leafcut]; positivity) hN u
    (F.firstStageSuccess leafcut x) x (by dsimp [delta]; positivity)
    (fun p hp => F.firstStageSuccess_goodRootSet_card leafcut x p hp) hfirst hfixed

end Erdos642.CampaignFe72210b.ForestBundle
