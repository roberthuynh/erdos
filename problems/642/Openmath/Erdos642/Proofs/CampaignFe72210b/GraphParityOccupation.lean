import Openmath.Erdos642.Proofs.CampaignFe72210b.ShoreOccupation
import Openmath.Erdos642.Proofs.CampaignFe72210b.TwoStepPaths
import Openmath.Erdos642.Proofs.CampaignFe72210b.RestrictedPaths

/-! Actual even-position graph path occupations and their genuine shore law. -/
namespace Erdos642.CampaignFe72210b
open SimpleGraph Matrix Erdos642.FiniteMarkov Erdos642.OccupationTail
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (s : Set V) [DecidablePred (· ∈ s)]

/-- The actual ambient vertex set of a finite set in the shore subtype. -/
def ambientShoreSet (S : Finset s) : Finset V :=
  S.map ⟨Subtype.val, Subtype.val_injective⟩

omit [Fintype V] [DecidableEq V] [DecidablePred (· ∈ s)] in
@[simp] theorem mem_ambientShoreSet (S : Finset s) (x : s) :
    x.val ∈ ambientShoreSet s S ↔ x ∈ S := by
  exact Finset.mem_map' ⟨Subtype.val, Subtype.val_injective⟩

omit [Fintype V] [DecidablePred (· ∈ s)] in
/-- Mapping an actual subtype trajectory preserves the counted set occupation. -/
theorem occupation_map_shore (S : Finset s) {n : ℕ} (x : s) (p : Path s n) :
    occupation (ambientShoreSet s S) x.val (mapPath Subtype.val p) = occupation S x p := by
  induction n generalizing x with
  | zero => simp [occupation, Chain.vertexSum]
  | succ n ih =>
    change (if x.val ∈ ambientShoreSet s S then 1 else 0) +
      occupation (ambientShoreSet s S) p.1.val (mapPath Subtype.val p.2) =
        (if x ∈ S then 1 else 0) + occupation S p.1 p.2
    simp only [mem_ambientShoreSet, ih]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exact actual event law, before any concentration inequality is applied. -/
theorem graph_even_shore_eventMass (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (n : ℕ)
    (E : V → Path V n → Prop) (x : s) :
    (graphChain G hdeg).eventMass (2 * n)
      (fun y p => E y (sampleEvenTwoMul n p)) x.val =
    (shoreChain G s t hbi hdeg).eventMass n
      (fun y p => E y.val (mapPath Subtype.val p)) x := by
  rw [(graphChain G hdeg).even_sample_eventMass]
  exact (graphChain G hdeg).twoStep.restriction_eventMass s
    (shoreChain G s t hbi hdeg) (fun _ _ => rfl)
    (fun y z hz => graphTransition_sq_zero_outside G hbi y.val z y.property hz)
    n E x

/-- The actual original graph walk's even-position occupation event equals the shore event. -/
theorem graph_even_shore_occupation_eventMass (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x)
    (S : Finset s) (n : ℕ) (a : ℝ) (x : s) :
    (graphChain G hdeg).eventMass (2 * n)
      (fun y p => occupation (ambientShoreSet s S) y (sampleEvenTwoMul n p) ≤ a) x.val =
    (shoreChain G s t hbi hdeg).eventMass n (fun y p => occupation S y p ≤ a) x := by
  simpa only [occupation_map_shore] using
    graph_even_shore_eventMass s G t hbi hdeg n
      (fun y p => occupation (ambientShoreSet s S) y p ≤ a) x

/-- Genuine graph-walk even-position occupation tail from original graph spectral premises. -/
theorem graph_even_shore_occupation_tail [Nonempty s] (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x)
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (S : Finset s) (n : ℕ) (x : s) :
    (graphChain G hdeg).eventMass (2 * n)
      (fun y p => occupation (ambientShoreSet s S) y (sampleEvenTwoMul n p) ≤
        ((n + 1 : ℕ) : ℝ) * Erdos642.TiltedOperator.mass S (shoreRoot G s) / 2) x.val ≤
      (2 / shoreRoot G s x ^ 2) * Real.exp
        (-γ * Erdos642.TiltedOperator.mass S (shoreRoot G s) * ((n + 1 : ℕ) : ℝ) / 64) := by
  rw [graph_even_shore_occupation_eventMass s G t hbi hdeg]
  have ht := shore_occupation_tail G s t hbi hdeg γ hgap S (n + 1) (by omega) x
  simpa using ht

end Erdos642.CampaignFe72210b
