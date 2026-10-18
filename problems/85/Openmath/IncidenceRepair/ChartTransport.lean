import Openmath.IncidenceRepair.CertificateGeometry

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair
variable {K : Type*} [Field K] {n : ℕ}

/-- The actual inclusion of a three-dimensional coordinate vector plane. -/
def chartLift (e : Fin 3 ↪ Fin (n + 1)) : Coordinates K 2 →ₗ[K] Coordinates K n where
  toFun v j := ∑ i, if e i = j then v i else 0
  map_add' v w := by
    classical
    ext j
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  map_smul' c v := by
    classical
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp

def chartRestrict (e : Fin 3 ↪ Fin (n + 1)) : Coordinates K n →ₗ[K] Coordinates K 2 where
  toFun v i := v (e i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem chartRestrict_lift (e : Fin 3 ↪ Fin (n + 1)) (v : Coordinates K 2) :
    chartRestrict e (chartLift e v) = v := by
  classical
  ext i
  simp [chartRestrict, chartLift, e.injective.eq_iff]

theorem chartLift_injective (e : Fin 3 ↪ Fin (n + 1)) :
    Function.Injective (chartLift (K := K) e) := by
  intro v w h
  simpa using congrArg (chartRestrict e) h

def ChartSupported (e : Fin 3 ↪ Fin (n + 1)) (v : Coordinates K n) : Prop :=
  ∀ j, j ∉ Set.range e → v j = 0

theorem chartLift_supported (e : Fin 3 ↪ Fin (n + 1)) (v : Coordinates K 2) :
    ChartSupported e (chartLift e v) := by
  classical
  intro j hj
  change ∑ i, (if e i = j then v i else 0) = 0
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg (fun h => hj ⟨i, h⟩)]

theorem chartLift_restrict (e : Fin 3 ↪ Fin (n + 1)) (v : Coordinates K n)
    (hv : ChartSupported e v) : chartLift e (chartRestrict e v) = v := by
  classical
  ext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    have h := congr_fun (chartRestrict_lift e (chartRestrict e v)) i
    exact h
  · rw [chartLift_supported e _ j hj, hv j hj]

theorem chartRestrict_ne_zero (e : Fin 3 ↪ Fin (n + 1)) (v : Coordinates K n)
    (hv : ChartSupported e v) (hne : v ≠ 0) : chartRestrict e v ≠ 0 := by
  intro hz
  apply hne
  rw [← chartLift_restrict e v hv, hz, map_zero]

theorem chartLift_dot (e : Fin 3 ↪ Fin (n + 1)) (v : Coordinates K 2)
    (w : Coordinates K n) :
    ∑ j, chartLift e v j * w j = ∑ i, v i * w (e i) := by
  classical
  change ∑ j, (∑ i, if e i = j then v i else 0) * w j = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [ite_mul, eq_comm]

theorem chartRestrict_dot_of_supported (e : Fin 3 ↪ Fin (n + 1))
    (v w : Coordinates K n) (hv : ChartSupported e v) :
    ∑ i, chartRestrict e v i * chartRestrict e w i = ∑ j, v j * w j := by
  rw [← chartLift_restrict e v hv] at ⊢
  rw [chartRestrict_lift, chartLift_dot]
  rfl

/-- Coordinate points/hyperplanes of a source chart, embedded in the full space. -/
def chartPoint (e : Fin 3 ↪ Fin (n + 1)) : Point K 2 → Point K n :=
  Projectivization.map (chartLift e) (chartLift_injective e)

def chartHyperplane (e : Fin 3 ↪ Fin (n + 1)) : Hyperplane K 2 → Hyperplane K n :=
  chartPoint e

/-- Restrict an image point to its intended plane; an escaping image is replaced by O. -/
def chartRestrictPoint (e : Fin 3 ↪ Fin (n + 1)) (p : Point K n) : Point K 2 := by
  classical
  exact if hp : ChartSupported e p.rep then
    Projectivization.mk K (chartRestrict e p.rep) (chartRestrict_ne_zero e p.rep hp p.rep_nonzero)
    else coordinatePoint 2

/-- Intersect a hyperplane containing the complementary coordinate span with the
chart plane. Otherwise use the chart infinity line. -/
def chartRestrictHyperplane (e : Fin 3 ↪ Fin (n + 1)) (H : Hyperplane K n) : Hyperplane K 2 :=
  chartRestrictPoint e H

theorem chart_restrict_incident (e : Fin 3 ↪ Fin (n + 1))
    (p : Point K n) (H : Hyperplane K n)
    (hp : ChartSupported e p.rep) (hH : ChartSupported e H.rep) :
    Incident (chartRestrictPoint e p) (chartRestrictHyperplane e H) ↔ Incident p H := by
  classical
  unfold chartRestrictHyperplane chartRestrictPoint
  simp only [dif_pos hp, dif_pos hH]
  unfold Incident
  rw [Projectivization.orthogonal_mk]
  have he := chartRestrict_dot_of_supported e p.rep H.rep hp
  change (∑ i, chartRestrict e p.rep i * chartRestrict e H.rep i = 0) ↔ _
  rw [he]
  have h := Projectivization.orthogonal_mk p.rep_nonzero H.rep_nonzero
  simpa only [Projectivization.mk_rep, dotProduct] using h.symm

theorem chart_point_supported_of_flags (e : Fin 3 ↪ Fin (n + 1)) (p : Point K n)
    (h : ∀ k, k ∉ Set.range e → Incident p (coordinateHyperplane k)) :
    ChartSupported e p.rep := by
  intro k hk
  exact (coordinateHyperplane_incident p k).mp (h k hk)

theorem chart_hyperplane_supported_of_flags (e : Fin 3 ↪ Fin (n + 1)) (H : Hyperplane K n)
    (h : ∀ k, k ∉ Set.range e → Incident (coordinatePoint k) H) :
    ChartSupported e H.rep := by
  intro k hk
  exact (coordinatePoint_incident k H).mp (h k hk)

/-- A failed induced flag is charged to an actual primary, membership, or
complementary-anchor flag. No escaping point or hyperplane is discarded for free. -/
theorem chart_error_witness {L : Type*} [Field L]
    (e : Fin 3 ↪ Fin (n + 1))
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (p : Point K n) (H : Hyperplane K n)
    (hpoints : ∀ k, k ∉ Set.range e → φ (coordinatePoint k) = coordinatePoint k)
    (hhyperplanes : ∀ k, k ∉ Set.range e → ψ (coordinateHyperplane k) = coordinateHyperplane k)
    (hbad : ¬ Incident (chartRestrictPoint e (φ p)) (chartRestrictHyperplane e (ψ H))) :
    ¬ Incident (φ p) (ψ H) ∨
      (∃ k, k ∉ Set.range e ∧ ¬ Incident (φ p) (ψ (coordinateHyperplane k))) ∨
      (∃ k, k ∉ Set.range e ∧ ¬ Incident (φ (coordinatePoint k)) (ψ H)) := by
  classical
  by_contra! h
  apply hbad
  apply (chart_restrict_incident e (φ p) (ψ H) ?_ ?_).2 h.1
  · apply chart_point_supported_of_flags
    intro k hk
    simpa only [hhyperplanes k hk] using h.2.1 k hk
  · apply chart_hyperplane_supported_of_flags
    intro k hk
    simpa only [hpoints k hk] using h.2.2 k hk

theorem chart_complement_card (e : Fin 3 ↪ Fin (n + 1)) :
    (Finset.univ.filter (fun k => k ∉ Set.range e)).card = n - 2 := by
  classical
  have he : (Finset.univ.image e).card = 3 := by
    rw [Finset.card_image_of_injective _ e.injective]
    simp
  have hset : Finset.univ.filter (fun k => k ∉ Set.range e) =
      Finset.univ \ Finset.univ.image e := by ext k; simp
  rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _), he]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

end Erdos85.IncidenceRepair
