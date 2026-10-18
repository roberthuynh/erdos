import Openmath.IncidenceRepair.ChartSlots
import Openmath.IncidenceRepair.WeightedPlane

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

variable {K L : Type*} [Field K] [Field L] {n : ℕ}

lemma chartPoint_supported (e : Fin 3 ↪ Fin (n + 1)) (p : Point K 2) :
    ChartSupported e (chartPoint e p).rep := by
  induction p using Projectivization.ind with
  | h v hv =>
    change ChartSupported e (Projectivization.mk K (chartLift e v) _).rep
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K (chartLift e v)
      (map_ne_zero_iff _ (chartLift_injective e) |>.mpr hv)
    rw [← hc]
    intro j hj
    simp [Pi.smul_apply, chartLift_supported e v j hj]

@[simp] lemma chartRestrictPoint_chartPoint (e : Fin 3 ↪ Fin (n + 1)) (p : Point K 2) :
    chartRestrictPoint e (chartPoint e p) = p := by
  classical
  unfold chartRestrictPoint
  rw [dif_pos (chartPoint_supported e p)]
  induction p using Projectivization.ind with
  | h v hv =>
    change Projectivization.mk K (chartRestrict e (Projectivization.mk K (chartLift e v) _).rep) _ =
      Projectivization.mk K v hv
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K (chartLift e v)
      (map_ne_zero_iff _ (chartLift_injective e) |>.mpr hv)
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
    refine ⟨c, ?_⟩
    rw [← hc]
    simp only [Units.smul_def, map_smul, chartRestrict_lift]

@[simp] lemma chartRestrictHyperplane_chartHyperplane (e : Fin 3 ↪ Fin (n + 1))
    (H : Hyperplane K 2) : chartRestrictHyperplane e (chartHyperplane e H) = H :=
  chartRestrictPoint_chartPoint e H

lemma chart_lift_incident (e : Fin 3 ↪ Fin (n + 1)) (p : Point K 2)
    (H : Hyperplane K 2) : Incident (chartPoint e p) (chartHyperplane e H) ↔ Incident p H := by
  simpa using (chart_restrict_incident e (chartPoint e p) (chartHyperplane e H)
    (chartPoint_supported e p) (chartPoint_supported e H)).symm

def inducedPointMap (e : Fin 3 ↪ Fin (n + 1)) (φ : Point K n → Point L n) :
    Point K 2 → Point L 2 := fun p => chartRestrictPoint e (φ (chartPoint e p))

def inducedHyperplaneMap (e : Fin 3 ↪ Fin (n + 1)) (ψ : Hyperplane K n → Hyperplane L n) :
    Hyperplane K 2 → Hyperplane L 2 := fun H => chartRestrictHyperplane e (ψ (chartHyperplane e H))

lemma induced_incident_of_good (e : Fin 3 ↪ Fin (n + 1))
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (p : Point K 2) (H : Hyperplane K 2)
    (hp : ChartSupported e (φ (chartPoint e p)).rep)
    (hH : ChartSupported e (ψ (chartHyperplane e H)).rep)
    (hgood : Incident (φ (chartPoint e p)) (ψ (chartHyperplane e H))) :
    Incident (inducedPointMap e φ p) (inducedHyperplaneMap e ψ H) :=
  (chart_restrict_incident e _ _ hp hH).mpr hgood

namespace Plane

lemma diagonal_forced_by_O_I (H : Hyperplane K 2)
    (hO : Incident (affine 0 0) H) (hI : Incident (affine 1 1) H) : H = slope 1 0 := by
  have hzero := (affine_incident_iff 0 0 H).mp hO
  have hsum := (affine_incident_iff 1 1 H).mp hI
  simp only [mul_zero, zero_add, zero_eq_neg] at hzero
  simp only [mul_one, hzero, neg_zero] at hsum
  rw [← Projectivization.mk_rep H]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨H.rep 1, ?_⟩
  ext i
  fin_cases i <;> simp [hzero]
  linear_combination -hsum

lemma W_forced_by_infinity_diagonal (p : Point K 2)
    (hInf : Incident p (infinity : Hyperplane K 2))
    (hd : Incident p (slope 1 0)) : p = W := by
  have hzero := (incident_infinity_iff p).mp hInf
  have hsum : p.rep 1 - p.rep 0 = 0 := by
    unfold Incident at hd
    rw [← Projectivization.mk_rep p] at hd
    unfold slope at hd
    rw [Projectivization.orthogonal_mk] at hd
    simp only [dotProduct, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, mul_neg, mul_one, mul_zero,
      neg_zero, add_zero] at hd
    change -p.rep 0 + p.rep 1 = 0 at hd
    linear_combination hd
  rw [← Projectivization.mk_rep p]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨p.rep 1, ?_⟩
  ext i
  fin_cases i <;> simp [hzero]
  linear_combination hsum

end Plane

/-- The five already protected line values and three coordinate point values. -/
structure ChartBase (e : Fin 3 ↪ Fin (n + 1))
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) : Prop where
  point_U : φ (chartPoint e Plane.U) = chartPoint e Plane.U
  point_V : φ (chartPoint e Plane.V) = chartPoint e Plane.V
  point_O : φ (chartPoint e (Plane.affine 0 0)) = chartPoint e (Plane.affine 0 0)
  line_infinity : ψ (chartHyperplane e Plane.infinity) = chartHyperplane e Plane.infinity
  line_vertical_zero : ψ (chartHyperplane e (Plane.vertical 0)) = chartHyperplane e (Plane.vertical 0)
  line_vertical_one : ψ (chartHyperplane e (Plane.vertical 1)) = chartHyperplane e (Plane.vertical 1)
  line_horizontal_zero : ψ (chartHyperplane e (Plane.horizontal 0)) = chartHyperplane e (Plane.horizontal 0)
  line_horizontal_one : ψ (chartHyperplane e (Plane.horizontal 1)) = chartHyperplane e (Plane.horizontal 1)
  complement_points : ∀ k, k ∉ Set.range e → φ (coordinatePoint k) = coordinatePoint k
  complement_hyperplanes : ∀ k, k ∉ Set.range e → ψ (coordinateHyperplane k) = coordinateHyperplane k

def extraPoint (i : Fin 4) : Point K 2 :=
  ![Plane.affine 1 1, Plane.W, Plane.affine 1 0, Plane.affine 0 1] i

def extraLeft (i : Fin 4) : Hyperplane K 2 :=
  ![Plane.vertical 1, Plane.infinity, Plane.vertical 1, Plane.vertical 0] i

def extraRight (i : Fin 4) : Hyperplane K 2 :=
  ![Plane.horizontal 1, Plane.slope 1 0, Plane.horizontal 0, Plane.horizontal 1] i

/-- Original flags added for I,D,W,E,J, including every complementary membership flag. -/
structure ChartExtraFlags (e : Fin 3 ↪ Fin (n + 1))
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) : Prop where
  point_complement : ∀ i k, k ∉ Set.range e →
    Incident (φ (chartPoint e (extraPoint i))) (ψ (coordinateHyperplane k))
  point_left : ∀ i, Incident (φ (chartPoint e (extraPoint i))) (ψ (chartHyperplane e (extraLeft i)))
  point_right : ∀ i, Incident (φ (chartPoint e (extraPoint i))) (ψ (chartHyperplane e (extraRight i)))
  diagonal_complement : ∀ k, k ∉ Set.range e →
    Incident (φ (coordinatePoint k)) (ψ (chartHyperplane e (Plane.slope 1 0)))
  diagonal_O : Incident (φ (chartPoint e (Plane.affine 0 0))) (ψ (chartHyperplane e (Plane.slope 1 0)))
  diagonal_I : Incident (φ (chartPoint e (Plane.affine 1 1))) (ψ (chartHyperplane e (Plane.slope 1 0)))

theorem protected_of_chart_certificate (e : Fin 3 ↪ Fin (n + 1))
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (base : ChartBase e φ ψ) (flags : ChartExtraFlags e φ ψ) :
    Plane.Protected (inducedPointMap e φ) (inducedHyperplaneMap e ψ) := by
  have hp (i : Fin 4) : ChartSupported e (φ (chartPoint e (extraPoint i))).rep := by
    apply chart_point_supported_of_flags
    intro k hk
    simpa only [base.complement_hyperplanes k hk] using flags.point_complement i k hk
  have hD : ChartSupported e (ψ (chartHyperplane e (Plane.slope 1 0))).rep := by
    apply chart_hyperplane_supported_of_flags
    intro k hk
    simpa only [base.complement_points k hk] using flags.diagonal_complement k hk
  have hI : inducedPointMap e φ (Plane.affine 1 1) = Plane.affine 1 1 := by
    apply Plane.vertical_horizontal_intersection
    · have h := induced_incident_of_good e φ ψ _ _ (hp 0)
        (by change ChartSupported e (ψ (chartHyperplane e (Plane.vertical 1))).rep
            rw [base.line_vertical_one]; exact chartPoint_supported e _) (flags.point_left 0)
      simpa only [extraPoint, extraLeft, Matrix.cons_val_zero, inducedHyperplaneMap,
        base.line_vertical_one, chartRestrictHyperplane_chartHyperplane] using h
    · have h := induced_incident_of_good e φ ψ _ _ (hp 0)
        (by change ChartSupported e (ψ (chartHyperplane e (Plane.horizontal 1))).rep
            rw [base.line_horizontal_one]; exact chartPoint_supported e _) (flags.point_right 0)
      simpa only [extraPoint, extraRight, Matrix.cons_val_zero, inducedHyperplaneMap,
        base.line_horizontal_one, chartRestrictHyperplane_chartHyperplane] using h
  have hd : inducedHyperplaneMap e ψ (Plane.slope 1 0) = Plane.slope 1 0 := by
    apply Plane.diagonal_forced_by_O_I
    · have h := induced_incident_of_good e φ ψ _ _
        (by rw [base.point_O]; exact chartPoint_supported e _) hD flags.diagonal_O
      simpa only [inducedPointMap, base.point_O, chartRestrictPoint_chartPoint] using h
    · have h := induced_incident_of_good e φ ψ _ _ (hp 0) hD flags.diagonal_I
      change Incident (inducedPointMap e φ (Plane.affine 1 1)) _ at h
      simpa only [hI] using h
  have hleft (i : Fin 4) : Incident (inducedPointMap e φ (extraPoint i))
      (inducedHyperplaneMap e ψ (extraLeft i)) := by
    apply induced_incident_of_good e φ ψ _ _ (hp i) _ (flags.point_left i)
    fin_cases i <;> simp [extraLeft,
      base.line_vertical_one, base.line_vertical_zero, base.line_infinity] <;>
      exact chartPoint_supported e _
  have hright (i : Fin 4) : Incident (inducedPointMap e φ (extraPoint i))
      (inducedHyperplaneMap e ψ (extraRight i)) := by
    apply induced_incident_of_good e φ ψ _ _ (hp i) _ (flags.point_right i)
    fin_cases i
    · change ChartSupported e (ψ (chartHyperplane e (Plane.horizontal 1))).rep
      rw [base.line_horizontal_one]
      exact chartPoint_supported (K := L) e (Plane.horizontal 1)
    · exact hD
    · change ChartSupported e (ψ (chartHyperplane e (Plane.horizontal 0))).rep
      rw [base.line_horizontal_zero]
      exact chartPoint_supported (K := L) e (Plane.horizontal 0)
    · change ChartSupported e (ψ (chartHyperplane e (Plane.horizontal 1))).rep
      rw [base.line_horizontal_one]
      exact chartPoint_supported (K := L) e (Plane.horizontal 1)
  refine ⟨?_, ?_, ?_, hI, ?_, ?_, ?_, ?_, hd, ?_, ?_, ?_, ?_⟩
  · simp only [inducedPointMap, base.point_U, chartRestrictPoint_chartPoint]
  · simp only [inducedPointMap, base.point_V, chartRestrictPoint_chartPoint]
  · simp only [inducedPointMap, base.point_O, chartRestrictPoint_chartPoint]
  · apply Plane.W_forced_by_infinity_diagonal
    · simpa [extraPoint, extraLeft, inducedHyperplaneMap, base.line_infinity] using hleft 1
    · simpa [extraPoint, extraRight, hd] using hright 1
  · apply Plane.vertical_horizontal_intersection
    · simpa [extraPoint, extraLeft, inducedHyperplaneMap, base.line_vertical_one] using hleft 2
    · simpa [extraPoint, extraRight, inducedHyperplaneMap, base.line_horizontal_zero] using hright 2
  · apply Plane.vertical_horizontal_intersection
    · simpa [extraPoint, extraLeft, inducedHyperplaneMap, base.line_vertical_zero] using hleft 3
    · simpa [extraPoint, extraRight, inducedHyperplaneMap, base.line_horizontal_one] using hright 3
  · simp only [inducedHyperplaneMap, base.line_infinity, chartRestrictHyperplane_chartHyperplane]
  · simp only [inducedHyperplaneMap, base.line_vertical_zero, chartRestrictHyperplane_chartHyperplane]
  · simp only [inducedHyperplaneMap, base.line_vertical_one, chartRestrictHyperplane_chartHyperplane]
  · simp only [inducedHyperplaneMap, base.line_horizontal_zero, chartRestrictHyperplane_chartHyperplane]
  · simp only [inducedHyperplaneMap, base.line_horizontal_one, chartRestrictHyperplane_chartHyperplane]

abbrev ExtraCertificateSlot (e : Fin 3 ↪ Fin (n + 1)) :=
  Fin 5 × (ChartComplement e ⊕ Fin 2)

def pointExtraPair (e : Fin 3 ↪ Fin (n + 1)) (i : Fin 4)
    (s : ChartComplement e ⊕ Fin 2) : Point K n × Hyperplane K n :=
  match s with
  | .inl k => (chartPoint e (extraPoint i), coordinateHyperplane k)
  | .inr j => (chartPoint e (extraPoint i), chartHyperplane e
      (if j = 0 then extraLeft i else extraRight i))

def diagonalExtraPair (e : Fin 3 ↪ Fin (n + 1))
    (s : ChartComplement e ⊕ Fin 2) : Point K n × Hyperplane K n :=
  match s with
  | .inl k => (coordinatePoint k, chartHyperplane e (Plane.slope 1 0))
  | .inr j => (chartPoint e (if j = 0 then Plane.affine 0 0 else Plane.affine 1 1),
      chartHyperplane e (Plane.slope 1 0))

/-- Five groups of n original flags. Repetitions across groups remain counted slots. -/
def extraCertificatePair (e : Fin 3 ↪ Fin (n + 1)) (s : ExtraCertificateSlot e) :
    Point K n × Hyperplane K n :=
  Fin.lastCases (diagonalExtraPair e s.2) (fun i => pointExtraPair e i s.2) s.1

theorem extraCertificatePair_incident (e : Fin 3 ↪ Fin (n + 1)) (s : ExtraCertificateSlot e) :
    Incident (extraCertificatePair (K := K) e s).1 (extraCertificatePair (K := K) e s).2 := by
  rcases s with ⟨i, s⟩
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [extraCertificatePair, Fin.lastCases_last]
    cases s with
    | inl k =>
      change Incident (coordinatePoint (K := K) k) (chartHyperplane e (Plane.slope 1 0))
      exact (coordinatePoint_incident _ _).mpr (chartPoint_supported e _ k k.property)
    | inr j =>
      fin_cases j <;> simp [diagonalExtraPair, chart_lift_incident]
  · simp only [extraCertificatePair, Fin.lastCases_castSucc]
    cases s with
    | inl k =>
      change Incident (chartPoint e (extraPoint i)) (coordinateHyperplane k)
      exact (coordinateHyperplane_incident _ _).mpr (chartPoint_supported e _ k k.property)
    | inr j =>
      fin_cases i <;> fin_cases j <;>
        simp [pointExtraPair, extraPoint, extraLeft, extraRight,
          chart_lift_incident] <;>
        simp [Plane.W, Plane.infinity, Plane.slope, Incident,
          Projectivization.orthogonal_mk, dotProduct, Fin.sum_univ_succ]

/-- A typed original source flag, suitable for equivariant transport and counting. -/
def extraCertificateFlag (e : Fin 3 ↪ Fin (n + 1)) (s : ExtraCertificateSlot e) :
    SourceFlag K n := ⟨extraCertificatePair e s, extraCertificatePair_incident e s⟩

theorem extraCertificateSlot_card (e : Fin 3 ↪ Fin (n + 1)) (hn : 2 ≤ n) :
    Nat.card (ExtraCertificateSlot e) = 5 * n := by
  classical
  have hc : Nat.card (ChartComplement e) = n - 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact chart_complement_card e
  simp only [ExtraCertificateSlot, Nat.card_prod, Nat.card_sum, Nat.card_fin, hc]
  omega

theorem chartExtraFlags_of_good_slots (e : Fin 3 ↪ Fin (n + 1))
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hgood : ∀ s : ExtraCertificateSlot e,
      Incident (φ (extraCertificatePair e s).1) (ψ (extraCertificatePair e s).2)) :
    ChartExtraFlags e φ ψ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k hk
    simpa only [extraCertificatePair, Fin.lastCases_castSucc, pointExtraPair] using
      hgood ⟨i.castSucc, .inl ⟨k, hk⟩⟩
  · intro i
    have h := hgood ⟨i.castSucc, .inr 0⟩
    simp only [extraCertificatePair, Fin.lastCases_castSucc] at h
    simpa [pointExtraPair] using h
  · intro i
    have h := hgood ⟨i.castSucc, .inr 1⟩
    simp only [extraCertificatePair, Fin.lastCases_castSucc] at h
    simpa [pointExtraPair] using h
  · intro k hk
    simpa only [extraCertificatePair, Fin.lastCases_last, diagonalExtraPair] using
      hgood ⟨Fin.last 4, .inl ⟨k, hk⟩⟩
  · have h := hgood ⟨Fin.last 4, .inr 0⟩
    simp only [extraCertificatePair, Fin.lastCases_last] at h
    simpa [diagonalExtraPair] using h
  · have h := hgood ⟨Fin.last 4, .inr 1⟩
    simp only [extraCertificatePair, Fin.lastCases_last] at h
    simpa [diagonalExtraPair] using h

theorem protected_of_good_extra_slots (e : Fin 3 ↪ Fin (n + 1))
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (base : ChartBase e φ ψ)
    (hgood : ∀ s : ExtraCertificateSlot e,
      Incident (φ (extraCertificatePair e s).1) (ψ (extraCertificatePair e s).2)) :
    Plane.Protected (inducedPointMap e φ) (inducedHyperplaneMap e ψ) :=
  protected_of_chart_certificate e φ ψ base (chartExtraFlags_of_good_slots e φ ψ hgood)

end Erdos85.IncidenceRepair
