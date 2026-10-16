import Openmath.Erdos642.Proofs.CampaignFe72210b.RoundedForestOccupation
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathAvoidance

/-! Equality transport and genuine finite prefix/suffix transfer for two-window counts. -/
namespace Erdos642.FiniteMarkov
namespace PathTransport
variable {V : Type*}

def castPath {L T : ℕ} (h : L = T) (p : Path V L) : Path V T := h ▸ p

theorem future_castPath {L T : ℕ} (h : L = T) (p : Path V L) :
    PathCoordinates.future (castPath h p) = PathCoordinates.future p := by cases h; rfl

theorem coordinate_castPath {L T : ℕ} (h : L = T) (x : V) (p : Path V L) (i : ℕ) :
    PathCoordinates.coordinate x (castPath h p) i = PathCoordinates.coordinate x p i := by cases h; rfl

theorem actualSA_castPath {L T : ℕ} (h : L = T) (x : V) (p : Path V L) :
    PathAvoidance.actualSA x (castPath h p) ↔ PathAvoidance.actualSA x p := by cases h; rfl

end PathTransport
namespace Chain
variable {V : Type*} [Fintype V] (C : Chain V)

theorem weight_castPath {L T : ℕ} (h : L = T) (x : V) (p : Path V L) :
    C.weight x (PathTransport.castPath h p) = C.weight x p := by cases h; rfl

theorem endpoint_castPath {L T : ℕ} (h : L = T) (x : V) (p : Path V L) :
    C.endpoint x (PathTransport.castPath h p) = C.endpoint x p := by cases h; rfl

theorem eventMass_castPath {L T : ℕ} (h : L = T) (E : V → Path V L → Prop) (x : V) :
    C.eventMass T (fun y p => E y (PathTransport.castPath h.symm p)) x =
      C.eventMass L E x := by cases h; rfl

/-- Freezing the observed initial vertex leaves the actual event mass unchanged. -/
theorem eventMass_freeze_start (n : ℕ) (E : V → Path V n → Prop) (x : V) :
    C.eventMass n E x = C.eventMass n (fun _ p => E x p) x := by
  classical
  unfold eventMass
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : E x p <;> simp [hp]

end Chain
end Erdos642.FiniteMarkov

namespace Erdos642.CampaignFe72210b.ForestBundle
open Erdos642.FiniteMarkov
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A B : Finset V} {q m b : ℕ}
variable (F : Erdos642.CampaignFe72210b.ForestBundle G A B q m b)

/-- Actual two-window count inside a fixed prefix and suffix of the full path. -/
noncomputable def windowWeightedCountAt (C : Chain V) (off a g n suffix : ℕ)
    (x : V) (w : Path V ((suffix + ((n + g) + a)) + off)) : ℝ :=
  let pq := PathSplit.split off (suffix + ((n + g) + a)) w
  F.windowWeightedCount C a g n (C.endpoint x pq.1)
    (PathSplit.split ((n + g) + a) suffix pq.2).1

/-- Uniform actual core mass estimates survive arbitrary fixed prefix and suffix. -/
theorem windowWeightedCountAt_eventMass_le (C : Chain V) (off a g n suffix : ℕ)
    (threshold delta : ℝ)
    (hcore : ∀ y, C.eventMass ((n + g) + a)
      (fun z p => F.windowWeightedCount C a g n z p < threshold) y ≤ delta) (x : V) :
    C.eventMass ((suffix + ((n + g) + a)) + off)
      (fun y w => F.windowWeightedCountAt C off a g n suffix y w < threshold) x ≤ delta := by
  exact C.window_eventMass_le off ((n + g) + a) suffix
    (fun y p => F.windowWeightedCount C a g n y p < threshold) delta hcore x

variable [DecidableRel G.Adj]

/-- Rounded actual graph occupation for windows at any fixed offset. -/
theorem graph_rounded_windowWeightedCountAt_eventMass_le (d : ℕ)
    (F : Erdos642.CampaignFe72210b.ForestBundle G A B
      (ForestParameters.q d) (ForestParameters.m (Fintype.card V) d) (ForestParameters.b d))
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hdeg : ∀ x : V, 0 < G.degree x) (hd : 100000000 ≤ d)
    (hN : 2 * d ≤ Fintype.card V)
    (hmin : ∀ x : V, (d : ℝ) ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * (d : ℝ))
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ) (t : ℕ) (ht : 2 ≤ t)
    (hlarge : 1000000000000000000 ≤ (d : ℝ) * γ * (t : ℝ) / (Fintype.card V : ℝ))
    (off g suffix : ℕ) (x : V) :
    (graphChain G hdeg).eventMass ((suffix + (((t - 1) + g) + (t - 1))) + off)
      (fun y w => F.windowWeightedCountAt (graphChain G hdeg) off (t - 1) g (t - 1) suffix y w <
        (d : ℝ) * (t : ℝ)^2 / (1000000000000000000000000 * (Fintype.card V : ℝ))) x ≤
      400 * (Fintype.card V : ℝ)^2 * Real.exp (-γ * (t : ℝ) / 100000000000000000) := by
  apply F.windowWeightedCountAt_eventMass_le
  intro y
  rw [(graphChain G hdeg).eventMass_freeze_start]
  exact F.graph_rounded_two_window_low_weightedCount_eventMass_le
    d hbi hdeg hd hN hmin hmax γ hgap t ht hlarge g y

/-- Equality transport embeds the actual offset-window observable in length T. -/
theorem graph_rounded_windowWeightedCountAt_eventMass_le_of_eq (d : ℕ)
    (F : Erdos642.CampaignFe72210b.ForestBundle G A B
      (ForestParameters.q d) (ForestParameters.m (Fintype.card V) d) (ForestParameters.b d))
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hdeg : ∀ x : V, 0 < G.degree x) (hd : 100000000 ≤ d)
    (hN : 2 * d ≤ Fintype.card V)
    (hmin : ∀ x : V, (d : ℝ) ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * (d : ℝ))
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ) (t : ℕ) (ht : 2 ≤ t)
    (hlarge : 1000000000000000000 ≤ (d : ℝ) * γ * (t : ℝ) / (Fintype.card V : ℝ))
    (off g suffix T : ℕ) (hT : ((suffix + (((t - 1) + g) + (t - 1))) + off) = T) (x : V) :
    (graphChain G hdeg).eventMass T
      (fun y w => F.windowWeightedCountAt (graphChain G hdeg) off (t - 1) g (t - 1) suffix y
        (PathTransport.castPath hT.symm w) <
          (d : ℝ) * (t : ℝ)^2 / (1000000000000000000000000 * (Fintype.card V : ℝ))) x ≤
      400 * (Fintype.card V : ℝ)^2 * Real.exp (-γ * (t : ℝ) / 100000000000000000) := by
  cases hT
  exact graph_rounded_windowWeightedCountAt_eventMass_le d F
    hbi hdeg hd hN hmin hmax γ hgap t ht hlarge off g suffix x

end Erdos642.CampaignFe72210b.ForestBundle
