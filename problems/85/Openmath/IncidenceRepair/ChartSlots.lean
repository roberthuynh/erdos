import Openmath.IncidenceRepair.ChartFlags
import Openmath.IncidenceRepair.FlagAction

noncomputable section
open scoped BigOperators Classical
namespace Erdos85.IncidenceRepair
variable {K : Type*} [Field K] {n : ℕ}

abbrev ChartComplement (e : Fin 3 ↪ Fin (n + 1)) := {k // k ∉ Set.range e}
abbrev ChartSlotIndex (e : Fin 3 ↪ Fin (n + 1)) :=
  Unit ⊕ (ChartComplement e ⊕ ChartComplement e)

instance (e : Fin 3 ↪ Fin (n + 1)) : Fintype (ChartComplement e) := by
  classical
  exact Fintype.ofFinite _

theorem chartComplement_card (e : Fin 3 ↪ Fin (n + 1)) :
    Fintype.card (ChartComplement e) = n - 2 := by
  classical
  rw [Fintype.card_of_subtype (Finset.univ.filter (fun k => k ∉ Set.range e)) (by simp)]
  exact chart_complement_card e

theorem chartSlotIndex_card (e : Fin 3 ↪ Fin (n + 1)) (hn : 2 ≤ n) :
    Fintype.card (ChartSlotIndex e) = 2 * n - 3 := by
  simp only [ChartSlotIndex, Fintype.card_sum, Fintype.card_unit, chartComplement_card]
  omega

/-- Every cost slot is an actual source flag. Primary, plane-membership and
complementary-anchor incidences are retained separately with their multiplicity. -/
def chartOriginalSlot (e : Fin 3 ↪ Fin (n + 1)) (pH : SourceFlag K 2) :
    ChartSlotIndex e → SourceFlag K n
  | .inl _ => ⟨(chartPoint e pH.1.1, chartHyperplane e pH.1.2),
      (chart_incident_iff e _ _).2 pH.2⟩
  | .inr (.inl k) => ⟨(chartPoint e pH.1.1, coordinateHyperplane k.1),
      chartPoint_incident_complement e _ k.1 k.2⟩
  | .inr (.inr k) => ⟨(coordinatePoint k.1, chartHyperplane e pH.1.2),
      chartHyperplane_incident_complement e _ k.1 k.2⟩

def originalFlagError {L : Type*} [Field L]
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (f : SourceFlag K n) : ℝ := by
  classical
  exact if Incident (φ f.1.1) (ψ f.1.2) then 0 else 1

theorem originalFlagError_nonneg {L : Type*} [Field L]
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (f : SourceFlag K n) : 0 ≤ originalFlagError φ ψ f := by
  classical
  unfold originalFlagError
  split_ifs <;> norm_num

/-- The local induced error is bounded by the exact sum of 2n−3 original errors. -/
theorem chart_error_majorant {L : Type*} [Field L]
    (e : Fin 3 ↪ Fin (n + 1))
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hpoints : ∀ k, k ∉ Set.range e → φ (coordinatePoint k) = coordinatePoint k)
    (hhyperplanes : ∀ k, k ∉ Set.range e → ψ (coordinateHyperplane k) = coordinateHyperplane k)
    (pH : SourceFlag K 2) :
    (if Incident (chartRestrictPoint e (φ (chartPoint e pH.1.1)))
      (chartRestrictHyperplane e (ψ (chartHyperplane e pH.1.2))) then (0 : ℝ) else 1) ≤
      ∑ s : ChartSlotIndex e, originalFlagError φ ψ (chartOriginalSlot e pH s) := by
  classical
  split_ifs with hgood
  · exact Finset.sum_nonneg (fun s _ => originalFlagError_nonneg _ _ _)
  · have hbad := chart_error_witness e φ ψ (chartPoint e pH.1.1) (chartHyperplane e pH.1.2)
      hpoints hhyperplanes hgood
    have hex : ∃ s : ChartSlotIndex e,
        originalFlagError φ ψ (chartOriginalSlot e pH s) = 1 := by
      rcases hbad with h | ⟨k,hk,h⟩ | ⟨k,hk,h⟩
      · exact ⟨.inl (), by simp [originalFlagError, chartOriginalSlot, h]⟩
      · exact ⟨.inr (.inl ⟨k,hk⟩), by simp [originalFlagError, chartOriginalSlot, h]⟩
      · exact ⟨.inr (.inr ⟨k,hk⟩), by simp [originalFlagError, chartOriginalSlot, h]⟩
    obtain ⟨s, hs⟩ := hex
    rw [← hs]
    exact Finset.single_le_sum (fun t _ => originalFlagError_nonneg _ _ _) (Finset.mem_univ s)

end Erdos85.IncidenceRepair
