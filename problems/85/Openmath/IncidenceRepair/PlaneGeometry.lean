import Openmath.IncidenceRepair.Geometry

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair.Plane

variable {K : Type*} [Field K]

def affine (x y : K) : Point K 2 :=
  Projectivization.mk K ![x, y, 1] (by
    intro h
    have := congr_fun h 2
    simpa using this)

def vertical (x : K) : Hyperplane K 2 :=
  Projectivization.mk K ![1, 0, -x] (by
    intro h
    have := congr_fun h 0
    simpa using this)

def horizontal (y : K) : Hyperplane K 2 :=
  Projectivization.mk K ![0, 1, -y] (by
    intro h
    have := congr_fun h 1
    simpa using this)

def slope (a b : K) : Hyperplane K 2 :=
  Projectivization.mk K ![-a, 1, -b] (by
    intro h
    have := congr_fun h 1
    simpa using this)

def infinity : Hyperplane K 2 :=
  Projectivization.mk K ![0, 0, 1] (by
    intro h
    have := congr_fun h 2
    simpa using this)

def U : Point K 2 := vertical 0
def V : Point K 2 := horizontal 0
def W : Point K 2 :=
  Projectivization.mk K ![1, 1, 0] (by
    intro h
    have := congr_fun h 0
    simpa using this)

@[simp] theorem affine_incident_vertical (x y t : K) :
    Incident (affine x y) (vertical t) ↔ x = t := by
  simp [Incident, affine, vertical, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ, sub_eq_zero, ← sub_eq_add_neg]

@[simp] theorem affine_incident_horizontal (x y t : K) :
    Incident (affine x y) (horizontal t) ↔ y = t := by
  simp [Incident, affine, horizontal, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ, sub_eq_zero, ← sub_eq_add_neg]

@[simp] theorem affine_incident_slope (x y a b : K) :
    Incident (affine x y) (slope a b) ↔ y = a * x + b := by
  simp only [Incident, affine, slope, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    add_zero, mul_one, one_mul, mul_neg]
  constructor <;> intro h <;> linear_combination h

@[simp] theorem affine_not_infinity (x y : K) :
    ¬ Incident (affine x y) (infinity : Hyperplane K 2) := by
  simp [Incident, affine, infinity, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ]

theorem incident_vertical_iff (p : Point K 2) (x : K) :
    Incident p (vertical x) ↔ p.rep 0 = x * p.rep 2 := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  simp only [vertical, Incident, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    mul_one, mul_zero, add_zero, zero_add, mul_neg]
  change p.rep 0 + -(p.rep 2 * x) = 0 ↔ _
  constructor <;> intro h <;> linear_combination h

theorem incident_horizontal_iff (p : Point K 2) (y : K) :
    Incident p (horizontal y) ↔ p.rep 1 = y * p.rep 2 := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  simp only [horizontal, Incident, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    mul_one, mul_zero, add_zero, zero_add, mul_neg]
  change p.rep 1 + -(p.rep 2 * y) = 0 ↔ _
  constructor <;> intro h <;> linear_combination h

theorem incident_infinity_iff (p : Point K 2) :
    Incident p (infinity : Hyperplane K 2) ↔ p.rep 2 = 0 := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  simp only [infinity, Incident, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    mul_one, mul_zero, add_zero, zero_add]
  rfl

theorem vertical_horizontal_intersection (p : Point K 2) (x y : K)
    (hx : Incident p (vertical x)) (hy : Incident p (horizontal y)) :
    p = affine x y := by
  have h0 := (incident_vertical_iff p x).1 hx
  have h1 := (incident_horizontal_iff p y).1 hy
  rw [← Projectivization.mk_rep p]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨p.rep 2, ?_⟩
  ext i
  fin_cases i <;> simp [affine, h0, h1, mul_comm]

theorem affine_injective : Function.Injective (fun z : K × K => affine z.1 z.2) := by
  intro x y h
  change affine x.1 x.2 = affine y.1 y.2 at h
  have hv : Incident (affine x.1 x.2) (vertical y.1) := by rw [h]; simp
  have hh : Incident (affine x.1 x.2) (horizontal y.2) := by rw [h]; simp
  exact Prod.ext ((affine_incident_vertical _ _ _).1 hv)
    ((affine_incident_horizontal _ _ _).1 hh)

theorem affine_incident_iff (x y : K) (H : Hyperplane K 2) :
    Incident (affine x y) H ↔ H.rep 0 * x + H.rep 1 * y = -H.rep 2 := by
  conv_lhs => rw [← Projectivization.mk_rep H]
  simp only [affine, Incident, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    one_mul, add_zero]
  change x * H.rep 0 + (y * H.rep 1 + H.rep 2) = 0 ↔ _
  constructor <;> intro h <;> linear_combination h

theorem coefficients_nonzero (H : Hyperplane K 2) :
    H.rep 0 ≠ 0 ∨ H.rep 1 ≠ 0 ∨ H.rep 2 ≠ 0 := by
  by_contra! h
  apply H.rep_nonzero
  ext i
  fin_cases i <;> simp [h.1, h.2.1, h.2.2]

theorem V_incident_iff (H : Hyperplane K 2) :
    Incident (V : Point K 2) H ↔ H.rep 1 = 0 := by
  conv_lhs => rw [← Projectivization.mk_rep H]
  simp only [V, horizontal, Incident, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    one_mul, zero_mul, neg_zero, add_zero, zero_add]
  rfl

theorem U_incident_iff (H : Hyperplane K 2) :
    Incident (U : Point K 2) H ↔ H.rep 0 = 0 := by
  conv_lhs => rw [← Projectivization.mk_rep H]
  simp only [U, vertical, Incident, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    one_mul, zero_mul, neg_zero, add_zero, zero_add]

theorem line_eq_infinity (H : Hyperplane K 2)
    (h0 : H.rep 0 = 0) (h1 : H.rep 1 = 0) : H = infinity := by
  rw [← Projectivization.mk_rep H]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨H.rep 2, ?_⟩
  ext i
  fin_cases i <;> simp [h0, h1]

theorem vertical_of_V_incident (H : Hyperplane K 2)
    (hV : Incident (V : Point K 2) H) (hne : H ≠ infinity) :
    ∃ x, H = vertical x := by
  have h1 := (V_incident_iff H).1 hV
  have h0 : H.rep 0 ≠ 0 := by
    intro hz
    exact hne (line_eq_infinity H hz h1)
  refine ⟨-H.rep 2 / H.rep 0, ?_⟩
  rw [← Projectivization.mk_rep H]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨H.rep 0, ?_⟩
  ext i
  fin_cases i <;> simp [h1]
  field_simp

theorem horizontal_of_U_incident (H : Hyperplane K 2)
    (hU : Incident (U : Point K 2) H) (hne : H ≠ infinity) :
    ∃ y, H = horizontal y := by
  have h0 := (U_incident_iff H).1 hU
  have h1 : H.rep 1 ≠ 0 := by
    intro hz
    exact hne (line_eq_infinity H h0 hz)
  refine ⟨-H.rep 2 / H.rep 1, ?_⟩
  rw [← Projectivization.mk_rep H]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨H.rep 1, ?_⟩
  ext i
  fin_cases i <;> simp [h0]
  field_simp

theorem vertical_ne_infinity (x : K) : vertical x ≠ (infinity : Hyperplane K 2) := by
  intro h
  have hx : Incident (affine x 0) (vertical x) := by simp
  rw [h] at hx
  exact affine_not_infinity x 0 hx

theorem horizontal_ne_infinity (y : K) : horizontal y ≠ (infinity : Hyperplane K 2) := by
  intro h
  have hy : Incident (affine 0 y) (horizontal y) := by simp
  rw [h] at hy
  exact affine_not_infinity 0 y hy

theorem vertical_injective : Function.Injective (vertical : K → Hyperplane K 2) := by
  intro x y h
  have hx : Incident (affine x 0) (vertical y) := by rw [← h]; simp
  exact (affine_incident_vertical _ _ _).1 hx

theorem horizontal_injective : Function.Injective (horizontal : K → Hyperplane K 2) := by
  intro x y h
  have hx : Incident (affine 0 x) (horizontal y) := by rw [← h]; simp
  exact (affine_incident_horizontal _ _ _).1 hx

@[simp] theorem V_on_vertical (x : K) : Incident (V : Point K 2) (vertical x) := by
  simp [V, horizontal, vertical, Incident, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ]

@[simp] theorem U_on_horizontal (y : K) : Incident (U : Point K 2) (horizontal y) := by
  simp [U, horizontal, vertical, Incident, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ]

theorem vertical_infinity_intersection (p : Point K 2) (x : K)
    (hx : Incident p (vertical x)) (hi : Incident p (infinity : Hyperplane K 2)) :
    p = V := by
  have h2 := (incident_infinity_iff p).1 hi
  have h0 := (incident_vertical_iff p x).1 hx
  rw [h2, mul_zero] at h0
  rw [← Projectivization.mk_rep p]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨p.rep 1, ?_⟩
  ext i
  fin_cases i <;> simp [V, horizontal, h0, h2]

theorem horizontal_infinity_intersection (p : Point K 2) (y : K)
    (hy : Incident p (horizontal y)) (hi : Incident p (infinity : Hyperplane K 2)) :
    p = U := by
  have h2 := (incident_infinity_iff p).1 hi
  have h1 := (incident_horizontal_iff p y).1 hy
  rw [h2, mul_zero] at h1
  rw [← Projectivization.mk_rep p]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨p.rep 0, ?_⟩
  ext i
  fin_cases i <;> simp [U, vertical, h1, h2]

@[simp] theorem V_not_on_slope (a b : K) : ¬ Incident (V : Point K 2) (slope a b) := by
  simp [V, horizontal, slope, Incident, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ]

theorem U_not_on_slope (a b : K) (ha : a ≠ 0) :
    ¬ Incident (U : Point K 2) (slope a b) := by
  simpa [U, vertical, slope, Incident, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ] using ha

theorem no_line_through_origin_U_V (H : Hyperplane K 2)
    (hO : Incident (affine 0 0) H)
    (hU : Incident (U : Point K 2) H) (hV : Incident (V : Point K 2) H) : False := by
  have h := line_eq_infinity H ((U_incident_iff H).1 hU) ((V_incident_iff H).1 hV)
  rw [h] at hO
  exact affine_not_infinity 0 0 hO

theorem W_incident_iff (H : Hyperplane K 2) :
    Incident (W : Point K 2) H ↔ H.rep 0 + H.rep 1 = 0 := by
  conv_lhs => rw [← Projectivization.mk_rep H]
  simp only [W, Incident, Projectivization.orthogonal_mk, dotProduct,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    one_mul, zero_mul, add_zero]
  rfl

theorem diagonal_of_W_incident (H : Hyperplane K 2)
    (hW : Incident (W : Point K 2) H) (hne : H ≠ infinity) :
    ∃ b, H = slope 1 b := by
  have hsum := (W_incident_iff H).1 hW
  have h1 : H.rep 1 ≠ 0 := by
    intro hz
    apply hne
    apply line_eq_infinity H _ hz
    linear_combination hsum - hz
  refine ⟨-H.rep 2 / H.rep 1, ?_⟩
  rw [← Projectivization.mk_rep H]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨H.rep 1, ?_⟩
  ext i
  fin_cases i
  · simp
    linear_combination -hsum
  · simp
  · simp
    field_simp

theorem slope_intercept_injective (a : K) : Function.Injective (slope a) := by
  intro b c h
  have hc : Incident (affine 0 b) (slope a c) := by rw [←h]; simp
  simpa using (affine_incident_slope 0 b a c).1 hc

end Erdos85.IncidenceRepair.Plane
