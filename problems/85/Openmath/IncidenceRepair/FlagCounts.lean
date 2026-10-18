import Openmath.IncidenceRepair.FlagAction
import Openmath.IncidenceRepair.GeometryDesign
import Openmath.IncidenceRepair.Target

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair
variable {K L : Type*} [Field K] [Field L] [Finite K] [Finite L] {n : ℕ}

lemma sourceFlag_card :
    Nat.card (SourceFlag K n) = pointCount K n * flagDegree K n := by
  classical
  letI : Fintype (Point K n) := Fintype.ofFinite _
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (Incident (K := K) (n := n))),
    Nat.card_sigma]
  simp only [incident_hyperplanes_card, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Fintype.card_eq_nat_card, point_card]
  rfl

lemma sourceFlag_nonempty (hn : 1 ≤ n) : Nonempty (SourceFlag K n) := by
  classical
  let j : Fin (n + 1) := ⟨1, by omega⟩
  have hv (i : Fin (n + 1)) : (Pi.single i 1 : Coordinates K n) ≠ 0 := by
    intro h
    have hi := congr_fun h i
    simpa using hi
  refine ⟨⟨(Projectivization.mk K (Pi.single 0 1) (hv 0),
    Projectivization.mk K (Pi.single j 1) (hv j)), ?_⟩⟩
  simp only [Incident, Projectivization.orthogonal_mk]
  have hj : j ≠ 0 := by simp [j]
  simp [hj, Ne.symm hj]

def sourceFlagError (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (F : SourceFlag K n) : ℝ := by
  classical
  exact if ¬ Incident (φ F.1.1) (ψ F.1.2) then 1 else 0

lemma sourceFlagError_nonneg (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (F : SourceFlag K n) :
    0 ≤ sourceFlagError φ ψ F := by
  unfold sourceFlagError
  split_ifs <;> norm_num

lemma sourceFlagError_sum [Fintype (SourceFlag K n)]
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    ∑ F : SourceFlag K n, sourceFlagError φ ψ F = (brokenFlags φ ψ : ℝ) := by
  classical
  unfold sourceFlagError
  rw [sum_indicator_eq_natCard]
  congr 1
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun pH : Point K n × Hyperplane K n => Incident pH.1 pH.2)
    (fun pH => ¬ Incident (φ pH.1) (ψ pH.2)))

/-- The unconditioned broken-flag fraction is exactly the published density T/(Nd). -/
lemma sourceFlagError_average [Fintype (SourceFlag K n)]
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    (∑ F : SourceFlag K n, sourceFlagError φ ψ F) / Fintype.card (SourceFlag K n) =
      errorDensity φ ψ := by
  rw [sourceFlagError_sum, Fintype.card_eq_nat_card, sourceFlag_card]
  simp only [Nat.cast_mul, errorDensity]

end Erdos85.IncidenceRepair
