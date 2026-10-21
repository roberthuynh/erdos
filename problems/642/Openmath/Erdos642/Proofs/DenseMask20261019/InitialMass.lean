import Openmath.Erdos642.Proofs.DenseMask20261019.InitialConcentration
import Openmath.Erdos642.Proofs.DenseMask20261019.GlobalObstruction

/-! Literal sampled expansion failure supplies the initial bad-history mass. -/
noncomputable section
namespace Erdos642.DenseMask20261019.InitialMass
open Finset SimpleGraph MeasureTheory ProbabilityTheory Real
open OAI.ErdosGallai.Sampling
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.DenseMask20261019
open InitialConcentration GlobalObstruction
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The literal original external neighborhood inside the actual sample. -/
def sampleBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (A U : Finset V) : Finset V :=
  (A \ U).filter (fun y => ∃ x ∈ U, G.Adj x y)

/-- Failure of the s external-vertex expansion inequality on a nonempty set
of size at most half the actual sampled order. -/
def sampledExpansionFailure (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℝ) :
    Set (V → Bool) :=
  {a | ∃ U : Finset V, U ⊆ sampleVertices a ∧ U.Nonempty ∧
    2*U.card ≤ (sampleVertices a).card ∧
    ((sampleBoundary G (sampleVertices a) U).card : ℝ) < s*(U.card : ℝ)}

theorem good_failure_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (d D s : ℝ) :
    sampledExpansionFailure G s ∩ {a | GoodSample G p d D a} ⊆
      boundedBadSamples G ((p : ℝ)*d) D s (3*(p : ℝ)*Fintype.card V/5) := by
  intro a ha
  obtain ⟨U, hUA, hUne, hhalf, hsmall⟩ := ha.1
  obtain ⟨hsize, hlo, hhi⟩ := ha.2
  refine ⟨(fun v _ => hlo v), hhi, U, sampleBoundary G (sampleVertices a) U,
    hUA, ?_, ?_, hUne, ?_, ?_, hsmall.le⟩
  · exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
  · apply Finset.disjoint_left.mpr
    intro v hvU hvB
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvB).1).2 hvU
  · have hh : 2*(U.card : ℝ) ≤ (sampleVertices a).card := by exact_mod_cast hhalf
    linarith
  · intro x hx y hy hxy
    by_cases hyU : y ∈ U
    · exact Or.inl hyU
    · exact Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hy, hyU⟩, x, hx, hxy⟩)

/-- The probability bridge uses the actual failure and good-sample events. -/
theorem bad_event_mass_of_failure (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (d D s : ℝ)
    (hfailure : 1/(Fintype.card V : ℝ)^4 ≤
      (sampleMeasure V p).real (sampledExpansionFailure G s))
    (hgood : (sampleMeasure V p).real {a | ¬GoodSample G p d D a} ≤
      1/(2*(Fintype.card V : ℝ)^4)) :
    1/(2*(Fintype.card V : ℝ)^4) ≤ (sampleMeasure V p).real
      (boundedBadSamples G ((p : ℝ)*d) D s (3*(p : ℝ)*Fintype.card V/5)) := by
  have hsub : sampledExpansionFailure G s ⊆
      boundedBadSamples G ((p : ℝ)*d) D s (3*(p : ℝ)*Fintype.card V/5) ∪
        {a | ¬GoodSample G p d D a} := by
    intro a ha
    by_cases hg : GoodSample G p d D a
    · exact Or.inl (good_failure_subset G p d D s ⟨ha, hg⟩)
    · exact Or.inr hg
  have hu := (measureReal_mono (μ := sampleMeasure V p) hsub (measure_ne_top _ _)).trans
    (measureReal_union_le (μ := sampleMeasure V p) _ _)
  have he : 1/(Fintype.card V : ℝ)^4 = 2*(1/(2*(Fintype.card V : ℝ)^4)) := by ring
  linarith

/-- Actual expansion-failure probability now pays initial concentration,
bad-size selection, pruning, deletion and fresh-mask integration. -/
theorem exists_failure_obstruction_constant :
    ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
    ∀ (p : unitInterval) (d D s : ℝ),
      1 ≤ Fintype.card V → 0 ≤ d → 1 ≤ D → 0 ≤ s → 16*D*s ≤ 1/10 →
      (∀ v, d ≤ (G.degree v : ℝ)) → (∀ v, (G.degree v : ℝ) ≤ D*d) →
      1000000*log (2*Fintype.card V) ≤ (p : ℝ)*d →
      1/(Fintype.card V : ℝ)^4 ≤ (sampleMeasure V p).real (sampledExpansionFailure G s) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ Fintype.card V ∧
        (k : ℝ) ≤ 3*(p : ℝ)*Fintype.card V/5 ∧ (p : ℝ)*d/4 ≤ k ∧
        (1/(4*(Fintype.card V : ℝ)^5))*exp (-(1+16*D)*(s*k)*log 2) ≤
          (experiment V p).real (obstructionEvent G C ((p : ℝ)*d) D k) := by
  obtain ⟨C, hC, hselected⟩ := exists_selected_obstruction_constant
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ havoid p d D s hn hd hD hs hsmall hlo hhi hr hfailure
  have hgood := bad_goodSample_probability G p d D hn hd hD hlo hhi hr
  have hmass := bad_event_mass_of_failure G p d D s hfailure hgood
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlog : 0 < log (2*(Fintype.card V : ℝ)) := log_pos (by linarith)
  have hrho : 0 < (p : ℝ)*d := by linarith
  exact hselected V G havoid p ((p : ℝ)*d) D s
    (3*(p : ℝ)*Fintype.card V/5) hn hrho hD hs hsmall hr hmass

end Erdos642.DenseMask20261019.InitialMass
