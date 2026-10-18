import Openmath.IncidenceRepair.ChartTransport
import Openmath.IncidenceRepair.WeightedPlane

noncomputable section
namespace Erdos85.IncidenceRepair
variable {K : Type*} [Field K] {n : ℕ}

lemma chart_supported_smul (e : Fin 3 ↪ Fin (n+1)) (v : Coordinates K n)
    (hv : ChartSupported e v) (a : K) : ChartSupported e (a • v) := by
  intro k hk
  simp [hv k hk]

lemma chart_supported_mk_rep (e : Fin 3 ↪ Fin (n+1)) (v : Coordinates K n)
    (hv : ChartSupported e v) (hne : v ≠ 0) :
    ChartSupported e (Projectivization.mk K v hne).rep := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hne
  rw [←ha]
  exact chart_supported_smul e v hv a

lemma chartHyperplane_supported (e : Fin 3 ↪ Fin (n+1)) (H : Hyperplane K 2) :
    ChartSupported e (chartHyperplane e H).rep := by
  induction H using Projectivization.ind with
  | h v hv =>
    simp only [chartHyperplane, chartPoint, Projectivization.map_mk]
    exact chart_supported_mk_rep e _ (chartLift_supported e v) _

lemma chartHyperplane_restrict (e : Fin 3 ↪ Fin (n+1)) (H : Hyperplane K n)
    (hs : ChartSupported e H.rep) :
    chartHyperplane e (chartRestrictHyperplane e H) = H := by
  classical
  unfold chartRestrictHyperplane chartRestrictPoint
  rw [dif_pos hs]
  simp only [chartHyperplane, chartPoint, Projectivization.map_mk]
  have h := chartLift_restrict e H.rep hs
  convert Projectivization.mk_rep H using 1
  congr 1

lemma chartRestrictHyperplane_lift (e : Fin 3 ↪ Fin (n+1)) (H : Hyperplane K 2) :
    chartRestrictHyperplane e (chartHyperplane e H) = H := by
  apply Projectivization.map_injective (chartLift e) (chartLift_injective e)
  exact chartHyperplane_restrict e _ (chartHyperplane_supported e H)

lemma coordinatePoint_two_eq_infinity :
    coordinatePoint (K := K) (n := 2) 2 = Plane.infinity := by
  unfold coordinatePoint Plane.infinity
  congr 1
  ext i
  fin_cases i <;> simp

/-- A proper local vertical is equivalent to one actual global lifted vertical.
The default infinity output cannot pass the properness test. -/
theorem restricted_vertical_iff (e : Fin 3 ↪ Fin (n+1)) (H : Hyperplane K n) :
    (∃ t, chartRestrictHyperplane e H = Plane.vertical t) ↔
      ∃ t, H = chartHyperplane e (Plane.vertical t) := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    have hs : ChartSupported e H.rep := by
      by_contra hn
      have hd : chartRestrictHyperplane e H = Plane.infinity := by
        simp [chartRestrictHyperplane, chartRestrictPoint, hn, coordinatePoint_two_eq_infinity]
      exact Plane.vertical_ne_infinity t (ht.symm.trans hd)
    refine ⟨t, ?_⟩
    rw [←ht]
    exact (chartHyperplane_restrict e H hs).symm
  · rintro ⟨t, rfl⟩
    exact ⟨t, chartRestrictHyperplane_lift e _⟩

theorem restricted_horizontal_iff (e : Fin 3 ↪ Fin (n+1)) (H : Hyperplane K n) :
    (∃ t, chartRestrictHyperplane e H = Plane.horizontal t) ↔
      ∃ t, H = chartHyperplane e (Plane.horizontal t) := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    have hs : ChartSupported e H.rep := by
      by_contra hn
      have hd : chartRestrictHyperplane e H = Plane.infinity := by
        simp [chartRestrictHyperplane, chartRestrictPoint, hn, coordinatePoint_two_eq_infinity]
      exact Plane.horizontal_ne_infinity t (ht.symm.trans hd)
    refine ⟨t, ?_⟩
    rw [←ht]
    exact (chartHyperplane_restrict e H hs).symm
  · rintro ⟨t, rfl⟩
    exact ⟨t, chartRestrictHyperplane_lift e _⟩

lemma chart_axis_ne_zero (e : Fin 3 ↪ Fin (n+1)) (he : e 2 = 0)
    (i : Fin 3) (hi : i ≠ 2) : e i ≠ 0 := by
  intro h
  exact hi (e.injective (h.trans he.symm))

lemma chartHyperplane_vertical (e : Fin 3 ↪ Fin (n+1)) (he : e 2 = 0) (t : K) :
    chartHyperplane e (Plane.vertical t) =
      pencilHyperplane (e 0) (chart_axis_ne_zero e he 0 (by decide)) t := by
  classical
  simp only [chartHyperplane, chartPoint, Plane.vertical, Projectivization.map_mk,
    pencilHyperplane]
  congr 1
  ext j
  simp [chartLift, Fin.sum_univ_succ, Pi.single_apply, he, eq_comm]
  split_ifs <;> ring

lemma chartHyperplane_horizontal (e : Fin 3 ↪ Fin (n+1)) (he : e 2 = 0) (t : K) :
    chartHyperplane e (Plane.horizontal t) =
      pencilHyperplane (e 1) (chart_axis_ne_zero e he 1 (by decide)) t := by
  classical
  simp only [chartHyperplane, chartPoint, Plane.horizontal, Projectivization.map_mk,
    pencilHyperplane]
  congr 1
  ext j
  simp [chartLift, Fin.sum_univ_succ, Pi.single_apply, he, eq_comm]
  split_ifs <;> ring

variable {L : Type*} [Field L]

def globalProper (ψ : Hyperplane K n → Hyperplane L n)
    (i : Fin (n+1)) (hi : i ≠ 0) (t : K) : Prop :=
  ∃ c, ψ (pencilHyperplane i hi t) = pencilHyperplane i hi c

def globalCoordinate (ψ : Hyperplane K n → Hyperplane L n)
    (i : Fin (n+1)) (hi : i ≠ 0) (t : K) : L := by
  classical
  exact if h : globalProper ψ i hi t then Classical.choose h else 0

def inducedHyperplanes (e : Fin 3 ↪ Fin (n+1))
    (ψ : Hyperplane K n → Hyperplane L n) : Hyperplane K 2 → Hyperplane L 2 :=
  fun H => chartRestrictHyperplane e (ψ (chartHyperplane e H))

theorem properX_shared (e : Fin 3 ↪ Fin (n+1)) (he : e 2 = 0)
    (ψ : Hyperplane K n → Hyperplane L n) (t : K) :
    Plane.ProperX (inducedHyperplanes e ψ) t ↔
      globalProper ψ (e 0) (chart_axis_ne_zero e he 0 (by decide)) t := by
  unfold Plane.ProperX inducedHyperplanes globalProper
  rw [restricted_vertical_iff]
  simp_rw [chartHyperplane_vertical e he]

theorem properY_shared (e : Fin 3 ↪ Fin (n+1)) (he : e 2 = 0)
    (ψ : Hyperplane K n → Hyperplane L n) (t : K) :
    Plane.ProperY (inducedHyperplanes e ψ) t ↔
      globalProper ψ (e 1) (chart_axis_ne_zero e he 1 (by decide)) t := by
  unfold Plane.ProperY inducedHyperplanes globalProper
  rw [restricted_horizontal_iff]
  simp_rw [chartHyperplane_horizontal e he]

theorem globalCoordinate_image (ψ : Hyperplane K n → Hyperplane L n)
    (i : Fin (n+1)) (hi : i ≠ 0) (t : K) (ht : globalProper ψ i hi t) :
    ψ (pencilHyperplane i hi t) = pencilHyperplane i hi (globalCoordinate ψ i hi t) := by
  rw [globalCoordinate, dif_pos ht]
  exact Classical.choose_spec ht

/-- The zero-extended plane scalar is the exact SAME global pencil scalar. -/
theorem coordX_shared (e : Fin 3 ↪ Fin (n+1)) (he : e 2 = 0)
    (ψ : Hyperplane K n → Hyperplane L n) (t : K) :
    Plane.coordX (inducedHyperplanes e ψ) t =
      globalCoordinate ψ (e 0) (chart_axis_ne_zero e he 0 (by decide)) t := by
  classical
  by_cases hx : Plane.ProperX (inducedHyperplanes e ψ) t
  · have hg := (properX_shared e he ψ t).1 hx
    apply Plane.coordX_of_image
    unfold inducedHyperplanes
    rw [chartHyperplane_vertical e he, globalCoordinate_image ψ _ _ t hg]
    rw [←chartHyperplane_vertical e he]
    exact chartRestrictHyperplane_lift e _
  · have hg : ¬ globalProper ψ (e 0) (chart_axis_ne_zero e he 0 (by decide)) t := by
      exact fun h => hx ((properX_shared e he ψ t).2 h)
    simp [Plane.coordX, globalCoordinate, hx, hg]

theorem coordY_shared (e : Fin 3 ↪ Fin (n+1)) (he : e 2 = 0)
    (ψ : Hyperplane K n → Hyperplane L n) (t : K) :
    Plane.coordY (inducedHyperplanes e ψ) t =
      globalCoordinate ψ (e 1) (chart_axis_ne_zero e he 1 (by decide)) t := by
  classical
  by_cases hy : Plane.ProperY (inducedHyperplanes e ψ) t
  · have hg := (properY_shared e he ψ t).1 hy
    apply Plane.coordY_of_image
    unfold inducedHyperplanes
    rw [chartHyperplane_horizontal e he, globalCoordinate_image ψ _ _ t hg]
    rw [←chartHyperplane_horizontal e he]
    exact chartRestrictHyperplane_lift e _
  · have hg : ¬ globalProper ψ (e 1) (chart_axis_ne_zero e he 1 (by decide)) t := by
      exact fun h => hy ((properY_shared e he ψ t).2 h)
    simp [Plane.coordY, globalCoordinate, hy, hg]

end Erdos85.IncidenceRepair
