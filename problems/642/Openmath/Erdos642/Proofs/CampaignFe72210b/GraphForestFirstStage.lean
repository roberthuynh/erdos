import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestFirstStage
import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphOccupation

/-! Graph spectral hypotheses discharge the fixed-leaf-union first-stage input. -/
namespace Erdos642.CampaignFe72210b
open SimpleGraph Erdos642.FiniteMarkov Erdos642.OccupationTail
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Ambient finite subsets of a shore have the actual original-walk occupation bound. -/
theorem graph_occupation_tail_finset (A B : Finset V)
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hdeg : ∀ x : V, 0 < G.degree x) (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d)
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (T : Finset V) (hT : T ⊆ B) (t : ℕ) (ht : 2 ≤ t) (x : V) :
    (graphChain G hdeg).eventMass (t - 1)
      (fun y p => occupation T y p < (t : ℝ) * (T.card : ℝ) / (300 * (Fintype.card V : ℝ))) x ≤
      (200 * (Fintype.card V : ℝ)) * Real.exp
        (-γ * (t : ℝ) * (T.card : ℝ) / (10000 * (Fintype.card V : ℝ))) := by
  let U : Finset (B : Set V) := T.subtype (fun v => v ∈ B)
  have hmap : ambientShoreSet (B : Set V) U = T := by
    exact Finset.subtype_map_of_mem hT
  have hcard : U.card = T.card := by
    have hh := congrArg Finset.card hmap
    simpa only [ambientShoreSet, Finset.card_map] using hh
  have hh := graph_occupation_tail G (B : Set V) (A : Set V) hbi.symm hdeg d hd hmin hmax γ hgap U t ht x
  simpa only [hmap, hcard] using hh

namespace ForestBundle
variable {G} {A B : Finset V} {q m b : ℕ}
variable (F : Erdos642.CampaignFe72210b.ForestBundle G A B q m b)

/-- Actual graph one-forest ceiling-half failure bound, with no probability supplier premise. -/
theorem graph_bad_forest_half_eventMass_le
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hdeg : ∀ x : V, 0 < G.degree x) (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d)
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (hb : 1 ≤ b) (hm : 1 ≤ m) (f : Fin q) (t : ℕ) (ht : 2 ≤ t) (x : V) :
    (graphChain G hdeg).eventMass (t - 1)
      (fun y p => (m + 1) / 2 ≤
        (F.badInForest f ((t : ℝ) * (b : ℝ) / (600 * (Fintype.card V : ℝ))) y p).card) x ≤
      (2 : ℝ) ^ m * (200 * (Fintype.card V : ℝ)) * Real.exp
        (-γ * (t : ℝ) * (((m + 1) / 2 * b : ℕ) : ℝ) / (10000 * (Fintype.card V : ℝ))) := by
  have : Nonempty V := ⟨x⟩
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hf : ∀ J : Finset (Fin m), J.card = (m + 1) / 2 → ∀ y : V,
      (graphChain G hdeg).eventMass (t - 1) (fun z p => occupation (F.leafUnion f J) z p <
        (t : ℝ) * ((F.leafUnion f J).card : ℝ) / (300 * (Fintype.card V : ℝ))) y ≤
        (200 * (Fintype.card V : ℝ)) * Real.exp
          (-γ * (t : ℝ) * (((m + 1) / 2 * b : ℕ) : ℝ) / (10000 * (Fintype.card V : ℝ))) := by
    intro J hJ y
    have hh := graph_occupation_tail_finset G A B hbi hdeg d hd hmin hmax γ hgap
      (F.leafUnion f J) (F.leafUnion_subset f J) t ht y
    simpa only [F.leafUnion_card, hJ] using hh
  have hh := F.bad_forest_half_eventMass_le (graphChain G hdeg) f t (by omega)
    (Fintype.card V : ℝ) hN hb hm _ (by positivity) hf x
  simpa only [mul_assoc] using hh

/-- Actual finite union over all q forests; no independence is assumed. -/
theorem graph_any_bad_forest_eventMass_le
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hdeg : ∀ x : V, 0 < G.degree x) (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d)
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (hb : 1 ≤ b) (hm : 1 ≤ m) (t : ℕ) (ht : 2 ≤ t) (x : V) :
    (graphChain G hdeg).eventMass (t - 1)
      (fun y p => ∃ f : Fin q, (m + 1) / 2 ≤
        (F.badInForest f ((t : ℝ) * (b : ℝ) / (600 * (Fintype.card V : ℝ))) y p).card) x ≤
      (q : ℝ) * ((2 : ℝ) ^ m * (200 * (Fintype.card V : ℝ)) * Real.exp
        (-γ * (t : ℝ) * (((m + 1) / 2 * b : ℕ) : ℝ) / (10000 * (Fintype.card V : ℝ)))) := by
  have hu := (graphChain G hdeg).eventMass_iUnion_le (n := t - 1)
    (fun f : Fin q => fun y p => (m + 1) / 2 ≤
      (F.badInForest f ((t : ℝ) * (b : ℝ) / (600 * (Fintype.card V : ℝ))) y p).card) x
  refine hu.trans ?_
  calc
    _ ≤ ∑ _f : Fin q, (2 : ℝ) ^ m * (200 * (Fintype.card V : ℝ)) * Real.exp
        (-γ * (t : ℝ) * (((m + 1) / 2 * b : ℕ) : ℝ) / (10000 * (Fintype.card V : ℝ))) := by
      apply Finset.sum_le_sum
      intro f _
      exact F.graph_bad_forest_half_eventMass_le hbi hdeg d hd hmin hmax γ hgap hb hm f t ht x
    _ = _ := by simp

end ForestBundle
end Erdos642.CampaignFe72210b
