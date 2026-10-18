import Openmath.IncidenceRepair.ProtectedCertificate
import Openmath.IncidenceRepair.SharedPencil

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair
variable {K L : Type*} [Field K] [Field L] {n : ℕ}

lemma chartPoint_coordinatePoint (e : Fin 3 ↪ Fin (n+1)) (i : Fin 3) :
    chartPoint e (coordinatePoint (K := K) i) = coordinatePoint (e i) := by
  classical
  simp only [chartPoint, coordinatePoint, Projectivization.map_mk]
  congr 1
  ext j
  change (∑ k : Fin 3, if e k = j then (Pi.single i (1:K)) k else 0) = _
  calc
    _ = ∑ k : Fin 3, if k = i then (if e i = j then (1:K) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = i
      · subst k; simp
      · simp [hk, Pi.single_apply, Ne.symm hk]
    _ = _ := by simp [Pi.single_apply, eq_comm]

lemma Plane.U_eq_coordinatePoint : (Plane.U : Point K 2) = coordinatePoint 0 := by
  unfold Plane.U Plane.vertical coordinatePoint
  congr 1
  ext i
  fin_cases i <;> simp

lemma Plane.V_eq_coordinatePoint : (Plane.V : Point K 2) = coordinatePoint 1 := by
  unfold Plane.V Plane.horizontal coordinatePoint
  congr 1
  ext i
  fin_cases i <;> simp

lemma Plane.O_eq_coordinatePoint : (Plane.affine 0 0 : Point K 2) = coordinatePoint 2 := by
  unfold Plane.affine coordinatePoint
  congr 1
  ext i
  fin_cases i <;> simp

/-- The global initial certificate supplies every base protection used by a chart. -/
theorem chartBase_from_initial (e : Fin 3 ↪ Fin (n+1)) (he : e 2 = 0)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hpoints : ∀ i, φ (coordinatePoint i) = coordinatePoint i)
    (hhyperplanes : ∀ i, ψ (coordinateHyperplane i) = coordinateHyperplane i)
    (hpencils : ∀ i (hi : i ≠ 0), ψ (pencilHyperplane i hi 1) = pencilHyperplane i hi 1) :
    ChartBase e φ ψ := by
  constructor
  · simpa only [Plane.U_eq_coordinatePoint, chartPoint_coordinatePoint] using hpoints (e 0)
  · simpa only [Plane.V_eq_coordinatePoint, chartPoint_coordinatePoint] using hpoints (e 1)
  · simpa only [Plane.O_eq_coordinatePoint, chartPoint_coordinatePoint] using hpoints (e 2)
  · simpa only [←coordinatePoint_two_eq_infinity, chartHyperplane, chartPoint_coordinatePoint,
      coordinateHyperplane] using hhyperplanes (e 2)
  · change ψ (chartPoint e Plane.U) = chartPoint e Plane.U
    simpa only [Plane.U_eq_coordinatePoint, chartPoint_coordinatePoint, coordinateHyperplane]
      using hhyperplanes (e 0)
  · simpa only [chartHyperplane_vertical e he] using
      hpencils (e 0) (chart_axis_ne_zero e he 0 (by decide))
  · change ψ (chartPoint e Plane.V) = chartPoint e Plane.V
    simpa only [Plane.V_eq_coordinatePoint, chartPoint_coordinatePoint, coordinateHyperplane]
      using hhyperplanes (e 1)
  · simpa only [chartHyperplane_horizontal e he] using
      hpencils (e 1) (chart_axis_ne_zero e he 1 (by decide))
  · intro k _; exact hpoints k
  · intro k _; exact hhyperplanes k

end Erdos85.IncidenceRepair
