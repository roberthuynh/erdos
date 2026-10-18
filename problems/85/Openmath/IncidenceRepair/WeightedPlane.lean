import Openmath.IncidenceRepair.PlaneGeometry

noncomputable section
namespace Erdos85.IncidenceRepair.Plane

variable {K L : Type*} [Field K] [Field L]

/-- Exactly the protected seven point and six line values in the written plane lemma. -/
structure Protected (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) : Prop where
  point_U : φ U = U
  point_V : φ V = V
  point_O : φ (affine 0 0) = affine 0 0
  point_I : φ (affine 1 1) = affine 1 1
  point_W : φ W = W
  point_E : φ (affine 1 0) = affine 1 0
  point_J : φ (affine 0 1) = affine 0 1
  line_infinity : ψ infinity = infinity
  line_diagonal : ψ (slope 1 0) = slope 1 0
  line_vertical_zero : ψ (vertical 0) = vertical 0
  line_vertical_one : ψ (vertical 1) = vertical 1
  line_horizontal_zero : ψ (horizontal 0) = horizontal 0
  line_horizontal_one : ψ (horizontal 1) = horizontal 1

def ProperX (ψ : Hyperplane K 2 → Hyperplane L 2) (x : K) : Prop :=
  ∃ t, ψ (vertical x) = vertical t

def ProperY (ψ : Hyperplane K 2 → Hyperplane L 2) (y : K) : Prop :=
  ∃ t, ψ (horizontal y) = horizontal t

def coordX (ψ : Hyperplane K 2 → Hyperplane L 2) (x : K) : L := by
  classical
  exact if h : ProperX ψ x then Classical.choose h else 0

def coordY (ψ : Hyperplane K 2 → Hyperplane L 2) (y : K) : L := by
  classical
  exact if h : ProperY ψ y then Classical.choose h else 0

theorem properX_iff (ψ : Hyperplane K 2 → Hyperplane L 2) (x : K) :
    ProperX ψ x ↔ Incident (V : Point L 2) (ψ (vertical x)) ∧
      ψ (vertical x) ≠ infinity := by
  constructor
  · rintro ⟨t, ht⟩
    rw [ht]
    exact ⟨V_on_vertical t, vertical_ne_infinity t⟩
  · rintro ⟨hV, hne⟩
    exact vertical_of_V_incident _ hV hne

theorem properY_iff (ψ : Hyperplane K 2 → Hyperplane L 2) (y : K) :
    ProperY ψ y ↔ Incident (U : Point L 2) (ψ (horizontal y)) ∧
      ψ (horizontal y) ≠ infinity := by
  constructor
  · rintro ⟨t, ht⟩
    rw [ht]
    exact ⟨U_on_horizontal t, horizontal_ne_infinity t⟩
  · rintro ⟨hU, hne⟩
    exact horizontal_of_U_incident _ hU hne

theorem image_vertical (ψ : Hyperplane K 2 → Hyperplane L 2) (x : K)
    (hx : ProperX ψ x) : ψ (vertical x) = vertical (coordX ψ x) := by
  rw [coordX, dif_pos hx]
  exact Classical.choose_spec hx

theorem image_horizontal (ψ : Hyperplane K 2 → Hyperplane L 2) (y : K)
    (hy : ProperY ψ y) : ψ (horizontal y) = horizontal (coordY ψ y) := by
  rw [coordY, dif_pos hy]
  exact Classical.choose_spec hy

theorem coordX_of_image (ψ : Hyperplane K 2 → Hyperplane L 2) (x : K) (t : L)
    (h : ψ (vertical x) = vertical t) : coordX ψ x = t := by
  exact vertical_injective ((image_vertical ψ x ⟨t,h⟩).symm.trans h)

theorem coordY_of_image (ψ : Hyperplane K 2 → Hyperplane L 2) (y : K) (t : L)
    (h : ψ (horizontal y) = horizontal t) : coordY ψ y = t := by
  exact horizontal_injective ((image_horizontal ψ y ⟨t,h⟩).symm.trans h)

theorem protected_values (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ) :
    ProperX ψ 0 ∧ ProperX ψ 1 ∧ ProperY ψ 0 ∧ ProperY ψ 1 ∧
    coordX ψ 0 = 0 ∧ coordX ψ 1 = 1 ∧ coordY ψ 0 = 0 ∧ coordY ψ 1 = 1 := by
  exact ⟨⟨0,hp.line_vertical_zero⟩, ⟨1,hp.line_vertical_one⟩,
    ⟨0,hp.line_horizontal_zero⟩, ⟨1,hp.line_horizontal_one⟩,
    coordX_of_image ψ 0 0 hp.line_vertical_zero,
    coordX_of_image ψ 1 1 hp.line_vertical_one,
    coordY_of_image ψ 0 0 hp.line_horizontal_zero,
    coordY_of_image ψ 1 1 hp.line_horizontal_one⟩

theorem product_of_good_coordinates (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (x y : K)
    (hx : ProperX ψ x) (hy : ProperY ψ y)
    (hv : Incident (φ (affine x y)) (ψ (vertical x)))
    (hh : Incident (φ (affine x y)) (ψ (horizontal y))) :
    φ (affine x y) = affine (coordX ψ x) (coordY ψ y) := by
  rw [image_vertical ψ x hx] at hv
  rw [image_horizontal ψ y hy] at hh
  exact vertical_horizontal_intersection _ _ _ hv hh

theorem mixed_X_collapseY (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (x y : K)
    (hx : ProperX ψ x) (hy : ψ (horizontal y) = infinity)
    (hv : Incident (φ (affine x y)) (ψ (vertical x)))
    (hh : Incident (φ (affine x y)) (ψ (horizontal y))) : φ (affine x y) = V := by
  rw [image_vertical ψ x hx] at hv
  rw [hy] at hh
  exact vertical_infinity_intersection _ _ hv hh

theorem mixed_collapseX_Y (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (x y : K)
    (hx : ψ (vertical x) = infinity) (hy : ProperY ψ y)
    (hv : Incident (φ (affine x y)) (ψ (vertical x)))
    (hh : Incident (φ (affine x y)) (ψ (horizontal y))) : φ (affine x y) = U := by
  rw [hx] at hv
  rw [image_horizontal ψ y hy] at hh
  exact horizontal_infinity_intersection _ _ hh hv

/-- A discrepancy of the proper coordinate sets on the diagonal forces one of
the two anchor, two coordinate, or diagonal flags to break. -/
theorem proper_agree_of_diagonal_good (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ) (t : K)
    (hV : Incident (φ V) (ψ (vertical t)))
    (hU : Incident (φ U) (ψ (horizontal t)))
    (hv : Incident (φ (affine t t)) (ψ (vertical t)))
    (hh : Incident (φ (affine t t)) (ψ (horizontal t)))
    (hd : Incident (φ (affine t t)) (ψ (slope 1 0))) :
    ProperX ψ t ↔ ProperY ψ t := by
  rw [hp.point_V] at hV
  rw [hp.point_U] at hU
  rw [hp.line_diagonal] at hd
  constructor
  · intro hx
    by_contra hy
    have hi : ψ (horizontal t) = infinity := by
      by_contra hn
      exact hy ((properY_iff ψ t).2 ⟨hU,hn⟩)
    have hv' := mixed_X_collapseY φ ψ t t hx hi hv hh
    rw [hv'] at hd
    exact V_not_on_slope 1 0 hd
  · intro hy
    by_contra hx
    have hi : ψ (vertical t) = infinity := by
      by_contra hn
      exact hx ((properX_iff ψ t).2 ⟨hV,hn⟩)
    have hu' := mixed_collapseX_Y φ ψ t t hi hy hv hh
    rw [hu'] at hd
    exact U_not_on_slope 1 0 one_ne_zero hd

/-- Opposite mixed coordinate types cannot both preserve all flags on one
origin pencil line. This is the geometric input to the sum-min estimate. -/
theorem pencil_mixed_obstruction (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ) (a t u : K)
    (htX : ProperX ψ t) (htY : ψ (horizontal (a*t)) = infinity)
    (huX : ψ (vertical u) = infinity) (huY : ProperY ψ (a*u))
    (htv : Incident (φ (affine t (a*t))) (ψ (vertical t)))
    (hth : Incident (φ (affine t (a*t))) (ψ (horizontal (a*t))))
    (huv : Incident (φ (affine u (a*u))) (ψ (vertical u)))
    (huh : Incident (φ (affine u (a*u))) (ψ (horizontal (a*u))))
    (htl : Incident (φ (affine t (a*t))) (ψ (slope a 0)))
    (hul : Incident (φ (affine u (a*u))) (ψ (slope a 0)))
    (hO : Incident (φ (affine 0 0)) (ψ (slope a 0))) : False := by
  have ht := mixed_X_collapseY φ ψ t (a*t) htX htY htv hth
  have hu := mixed_collapseX_Y φ ψ u (a*u) huX huY huv huh
  rw [ht] at htl
  rw [hu] at hul
  rw [hp.point_O] at hO
  exact no_line_through_origin_U_V _ hO hul htl

/-- The reciprocal pair supplies the non-collapse support lower bound. -/
theorem reciprocal_obstruction (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ) (a : K)
    (hY : ψ (horizontal a) = infinity) (hX : ψ (vertical a⁻¹) = infinity)
    (hpv : Incident (φ (affine 1 a)) (ψ (vertical 1)))
    (hph : Incident (φ (affine 1 a)) (ψ (horizontal a)))
    (hqv : Incident (φ (affine a⁻¹ 1)) (ψ (vertical a⁻¹)))
    (hqh : Incident (φ (affine a⁻¹ 1)) (ψ (horizontal 1)))
    (hpl : Incident (φ (affine 1 a)) (ψ (slope a 0)))
    (hql : Incident (φ (affine a⁻¹ 1)) (ψ (slope a 0)))
    (hO : Incident (φ (affine 0 0)) (ψ (slope a 0))) : False := by
  have ht := mixed_X_collapseY φ ψ 1 a ⟨1,hp.line_vertical_one⟩ hY hpv hph
  have hu := mixed_collapseX_Y φ ψ a⁻¹ 1 hX ⟨1,hp.line_horizontal_one⟩ hqv hqh
  rw [ht] at hpl
  rw [hu] at hql
  rw [hp.point_O] at hO
  exact no_line_through_origin_U_V _ hO hql hpl

def diagonalIntercept (ψ : Hyperplane K 2 → Hyperplane L 2) (b : K) : L := by
  classical
  exact if h : ∃ c, ψ (slope 1 b) = slope 1 c then Classical.choose h else 0

theorem diagonalIntercept_of_image (ψ : Hyperplane K 2 → Hyperplane L 2)
    (b : K) (c : L) (hc : ψ (slope 1 b) = slope 1 c) : diagonalIntercept ψ b = c := by
  have he : ∃ c, ψ (slope 1 b) = slope 1 c := ⟨c,hc⟩
  rw [diagonalIntercept, dif_pos he]
  exact slope_intercept_injective 1 ((Classical.choose_spec he).symm.trans hc)

theorem protected_intercept_zero (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ) :
    diagonalIntercept ψ 0 = 0 :=
  diagonalIntercept_of_image ψ 0 0 hp.line_diagonal

/-- The Pexider identity follows from the product identity and the two diagonal flags. -/
theorem pexider_of_product_and_flags (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ) (u b : K)
    (hprod : φ (affine u (u+b)) = affine (coordX ψ u) (coordY ψ (u+b)))
    (hW : Incident (φ W) (ψ (slope 1 b)))
    (hpflag : Incident (φ (affine u (u+b))) (ψ (slope 1 b))) :
    coordY ψ (u+b) = coordX ψ u + diagonalIntercept ψ b := by
  rw [hp.point_W] at hW
  rw [hprod] at hpflag
  have hne : ψ (slope 1 b) ≠ infinity := by
    intro hi
    rw [hi] at hpflag
    exact affine_not_infinity _ _ hpflag
  obtain ⟨c,hc⟩ := diagonal_of_W_incident _ hW hne
  rw [hc] at hpflag
  rw [diagonalIntercept_of_image ψ b c hc]
  simpa using (affine_incident_slope _ _ _ _).1 hpflag

/-- On the protected original diagonal, good coordinate flags force equal coordinates. -/
theorem equal_coordinates_of_diagonal (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ) (t : K)
    (hx : ProperX ψ t) (hy : ProperY ψ t)
    (hv : Incident (φ (affine t t)) (ψ (vertical t)))
    (hh : Incident (φ (affine t t)) (ψ (horizontal t)))
    (hd : Incident (φ (affine t t)) (ψ (slope 1 0))) :
    coordY ψ t = coordX ψ t := by
  have hp' := product_of_good_coordinates φ ψ t t hx hy hv hh
  rw [hp',hp.line_diagonal] at hd
  simpa using (affine_incident_slope _ _ _ _).1 hd

end Erdos85.IncidenceRepair.Plane
