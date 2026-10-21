import Openmath.Erdos642.Proofs.CampaignFe72210b.CycleSupport
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

                                                              
                                                               
namespace Erdos642.CampaignFe72210b

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The genuine ordinary simple random walk, with zero rows at isolated vertices. -/
noncomputable def graphTransition (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℝ := fun x y => G.adjMatrix ℝ x y / (G.degree x : ℝ)

/-- Symmetric normalized adjacency. Positive degree is required in its later uses. -/
noncomputable def normalizedAdjacency (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℝ := fun x y =>
  G.adjMatrix ℝ x y / (Real.sqrt (G.degree x : ℝ) * Real.sqrt (G.degree y : ℝ))

/-- The exact two simple extremal eigenvalues and remaining absolute gap. -/
def HasBipartiteSpectralGap (G : SimpleGraph V) [DecidableRel G.Adj] (γ : ℝ) : Prop :=
  let T : Module.End ℝ (EuclideanSpace ℝ V) := (normalizedAdjacency G).toEuclideanLin
  0 < γ ∧ γ ≤ 1 ∧ T.HasEigenvalue 1 ∧ T.HasEigenvalue (-1) ∧
    Module.finrank ℝ (T.eigenspace 1) = 1 ∧
    Module.finrank ℝ (T.eigenspace (-1)) = 1 ∧
    ∀ lam : ℝ, T.HasEigenvalue lam → lam ≠ 1 → lam ≠ -1 → |lam| ≤ 1 - γ

/-- The fixed block length used by the reviewed written integration. -/
noncomputable def spectralBlockLength (N : ℕ) (γ : ℝ) : ℕ :=
  ⌈(2 : ℝ) + Real.log (N : ℝ) / γ⌉₊

/-- A literal simple cycle with at least its length in actual chords. -/
def HasRichCycle (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length ≤ (chordEdges c).card

/-- Full explicit premises of the reviewed structural theorem. -/
def SpectralHostPremises (G : SimpleGraph V) [DecidableRel G.Adj] (γ : ℝ) : Prop :=
  let N := Fintype.card V
  let k := spectralBlockLength N γ
  3 ≤ N ∧ G.Connected ∧ G.IsBipartite ∧
    G.maxDegree ≤ 100 * G.minDegree ∧ HasBipartiteSpectralGap G γ ∧
    (10 : ℝ)^100 * (k : ℝ) / γ ≤ (G.minDegree : ℝ) ∧
    (10 : ℝ)^100 * (k : ℝ)^2 ≤ (N : ℝ)

/-- Open target proposition. No theorem inhabiting it is supplied here. -/
def SpectralCycleClaim : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (γ : ℝ),
    SpectralHostPremises G γ → HasRichCycle G

end Erdos642.CampaignFe72210b
