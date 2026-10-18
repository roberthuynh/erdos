import Openmath.IncidenceRepair.ChartFlags
import Openmath.IncidenceRepair.FlagAction

noncomputable section
open scoped BigOperators Classical
namespace Erdos85.IncidenceRepair
variable {K : Type*} [Field K] {n : ℕ}

abbrev CoordinateCertificateSlot (n : ℕ) := Σ i : Fin (n + 1), {j // j ≠ i}
abbrev UnitPencilCertificateSlot (n : ℕ) :=
  Σ i : {i : Fin (n + 1) // i ≠ 0}, Option {j : Fin (n + 1) // j ≠ 0 ∧ j ≠ i.1}
abbrev InitialCertificateSlot (n : ℕ) :=
  CoordinateCertificateSlot n ⊕ UnitPencilCertificateSlot n

theorem coordinateCertificateSlot_card (n : ℕ) :
    Fintype.card (CoordinateCertificateSlot n) = n * (n + 1) := by
  simp [CoordinateCertificateSlot, Fintype.card_sigma, mul_comm]

theorem unitPencilCertificateSlot_card (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (UnitPencilCertificateSlot n) = n * n := by
  have hpair (i : {i : Fin (n + 1) // i ≠ 0}) :
      Fintype.card {j : Fin (n + 1) // j ≠ 0 ∧ j ≠ i.1} = n - 1 := by
    have h := Fintype.card_subtype_compl (fun j : Fin (n + 1) => j = 0 ∨ j = i.1)
    simp only [not_or] at h
    rw [Fintype.card_subtype_eq_or_eq_of_ne i.2.symm] at h
    simpa using h
  simp only [UnitPencilCertificateSlot, Fintype.card_sigma, Fintype.card_option, hpair]
  have hplus : n - 1 + 1 = n := by omega
  rw [hplus]
  simp

theorem initialCertificateSlot_card (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (InitialCertificateSlot n) = 2 * n ^ 2 + n := by
  simp only [InitialCertificateSlot, Fintype.card_sum,
    coordinateCertificateSlot_card, unitPencilCertificateSlot_card n hn]
  ring

def coordinateCertificateFlag (s : CoordinateCertificateSlot n) : SourceFlag K n :=
  ⟨(coordinatePoint s.2.1, coordinateHyperplane s.1), by
    unfold Incident coordinateHyperplane coordinatePoint
    rw [Projectivization.orthogonal_mk]
    simp [dotProduct, Pi.single_apply, s.2.2, s.2.2.symm]⟩

def unitPencilCertificateFlag (s : UnitPencilCertificateSlot n) : SourceFlag K n :=
  match s.2 with
  | none => ⟨(onesPoint, pencilHyperplane s.1.1 s.1.2 1), by
      unfold Incident onesPoint pencilHyperplane
      rw [Projectivization.orthogonal_mk]
      simp [dotProduct, Pi.single_apply, Pi.sub_apply, Pi.smul_apply,
        Finset.sum_sub_distrib]⟩
  | some j => ⟨(coordinatePoint j.1, pencilHyperplane s.1.1 s.1.2 1), by
      unfold Incident coordinatePoint pencilHyperplane
      rw [Projectivization.orthogonal_mk, single_dotProduct]
      simp [j.2.1, j.2.2, Ne.symm j.2.2]⟩

def initialCertificateFlag (s : InitialCertificateSlot n) : SourceFlag K n :=
  match s with
  | .inl s => coordinateCertificateFlag s
  | .inr s => unitPencilCertificateFlag s

/-- The actual initial original flag certificate forces all coordinate hyperplanes
and unit pencils simultaneously. -/
theorem initial_certificate_forces {L : Type*} [Field L]
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hp : ∀ i, φ (coordinatePoint i) = coordinatePoint i)
    (hI : φ (onesPoint (K := K) (n := n)) = onesPoint)
    (hgood : ∀ s : InitialCertificateSlot n,
      Incident (φ (initialCertificateFlag s).1.1) (ψ (initialCertificateFlag s).1.2)) :
    (∀ i, ψ (coordinateHyperplane i) = coordinateHyperplane i) ∧
      (∀ (i : Fin (n + 1)) (hi : i ≠ 0), ψ (pencilHyperplane i hi 1) = pencilHyperplane i hi 1) := by
  constructor
  · apply normalized_coordinate_hyperplanes φ ψ hp
    intro i j hj
    exact hgood (.inl ⟨i, j, hj⟩)
  · apply normalized_unit_pencils φ ψ hp hI
    · intro i hi j hj0 hji
      exact hgood (.inr ⟨⟨i,hi⟩, some ⟨j,hj0,hji⟩⟩)
    · intro i hi
      exact hgood (.inr ⟨⟨i,hi⟩, none⟩)

end Erdos85.IncidenceRepair
