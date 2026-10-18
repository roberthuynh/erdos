import Openmath.IncidenceRepair.ChartTransport

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair
variable {K : Type*} [Field K] {n : ℕ}

theorem chartPoint_incident_complement (e : Fin 3 ↪ Fin (n + 1)) (p : Point K 2)
    (k : Fin (n + 1)) (hk : k ∉ Set.range e) :
    Incident (chartPoint e p) (coordinateHyperplane k) := by
  classical
  induction p using Projectivization.ind with
  | h v hv =>
    unfold chartPoint Incident coordinateHyperplane coordinatePoint
    rw [Projectivization.map_mk, Projectivization.orthogonal_mk]
    rw [dotProduct_single, mul_one]
    exact chartLift_supported e v k hk

theorem chartHyperplane_incident_complement (e : Fin 3 ↪ Fin (n + 1))
    (H : Hyperplane K 2) (k : Fin (n + 1)) (hk : k ∉ Set.range e) :
    Incident (coordinatePoint k) (chartHyperplane e H) := by
  classical
  induction H using Projectivization.ind with
  | h v hv =>
    unfold chartHyperplane chartPoint Incident coordinatePoint
    rw [Projectivization.map_mk, Projectivization.orthogonal_mk]
    rw [single_dotProduct, one_mul]
    exact chartLift_supported e v k hk

theorem chart_incident_iff (e : Fin 3 ↪ Fin (n + 1)) (p : Point K 2) (H : Hyperplane K 2) :
    Incident (chartPoint e p) (chartHyperplane e H) ↔ Incident p H := by
  classical
  induction p using Projectivization.ind with
  | h v hv =>
    induction H using Projectivization.ind with
    | h w hw =>
      unfold chartHyperplane chartPoint Incident
      simp only [Projectivization.map_mk, Projectivization.orthogonal_mk]
      change (∑ j, chartLift e v j * chartLift e w j = 0) ↔ (∑ i, v i * w i = 0)
      rw [chartLift_dot]
      have h : ∀ i, chartLift e w (e i) = w i := fun i =>
        congr_fun (chartRestrict_lift e w) i
      simp only [h]

theorem normalized_coordinate_hyperplanes {L : Type*} [Field L]
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hp : ∀ i, φ (coordinatePoint i) = coordinatePoint i)
    (hflags : ∀ i j, j ≠ i → Incident (φ (coordinatePoint j)) (ψ (coordinateHyperplane i))) :
    ∀ i, ψ (coordinateHyperplane i) = coordinateHyperplane i := by
  intro i
  apply hyperplane_forced_by_basis
  intro j hj
  simpa only [hp j] using hflags i j hj

theorem normalized_unit_pencils {L : Type*} [Field L]
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hp : ∀ i, φ (coordinatePoint i) = coordinatePoint i)
    (hI : φ (onesPoint (K := K) (n := n)) = onesPoint)
    (hflags : ∀ (i : Fin (n + 1)) (hi : i ≠ 0) j, j ≠ 0 → j ≠ i →
      Incident (φ (coordinatePoint j)) (ψ (pencilHyperplane i hi 1)))
    (hones : ∀ (i : Fin (n + 1)) (hi : i ≠ 0),
      Incident (φ (onesPoint (K := K) (n := n))) (ψ (pencilHyperplane i hi 1))) :
    ∀ (i : Fin (n + 1)) (hi : i ≠ 0), ψ (pencilHyperplane i hi 1) = pencilHyperplane i hi 1 := by
  intro i hi
  apply hyperplane_forced_by_ones
  · intro j hj0 hji
    simpa only [hp j] using hflags i hi j hj0 hji
  · simpa only [hI] using hones i hi

end Erdos85.IncidenceRepair
