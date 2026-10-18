import Openmath.IncidenceRepair.PlaneGeometry

/-! The exact twenty-four protected-plane flag distributions. Restrictions on
nonzero slopes are implemented with zero summands, so denominators remain q^k. -/
noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair.Plane
variable {K : Type*} [Field K] [Fintype K]

def avg1 (f : K → ℝ) : ℝ := (∑ x, f x) / Fintype.card K
def avg2 (f : K → K → ℝ) : ℝ := (∑ x, ∑ y, f x y) / (Fintype.card K : ℝ)^2
def avg3 (f : K → K → K → ℝ) : ℝ :=
  (∑ x, ∑ y, ∑ z, f x y z) / (Fintype.card K : ℝ)^3

theorem avg1_nonneg {f : K → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ avg1 f := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun x _ => h x)
  · positivity

theorem avg2_nonneg {f : K → K → ℝ} (h : ∀ x y, 0 ≤ f x y) : 0 ≤ avg2 f := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => h x y))
  · positivity

theorem avg3_nonneg {f : K → K → K → ℝ} (h : ∀ x y z, 0 ≤ f x y z) :
    0 ≤ avg3 f := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
      Finset.sum_nonneg (fun z _ => h x y z)))
  · positivity

/-- The entries follow the order of the published table, counting repeated flags. -/
def costTerm (b : Point K 2 → Hyperplane K 2 → ℝ) : Fin 24 → ℝ := by
  classical
  exact ![
    avg1 (fun x => b V (vertical x)),
    avg1 (fun y => b U (horizontal y)),
    avg2 (fun x y => b (affine x y) (vertical x)),
    avg2 (fun x y => b (affine x y) (horizontal y)),
    avg1 (fun t => b (affine t t) (vertical t)),
    avg1 (fun t => b (affine t t) (horizontal t)),
    avg1 (fun t => b (affine t t) (slope 1 0)),
    avg1 (fun a => if a ≠ 0 then b (affine 0 0) (slope a 0) else 0),
    avg2 (fun a t => if a ≠ 0 then b (affine t (a*t)) (slope a 0) else 0),
    avg1 (fun a => if a ≠ 0 then b (affine 1 a) (vertical 1) else 0),
    avg1 (fun a => if a ≠ 0 then b (affine 1 a) (horizontal a) else 0),
    avg1 (fun a => if a ≠ 0 then b (affine a⁻¹ 1) (vertical a⁻¹) else 0),
    avg1 (fun a => if a ≠ 0 then b (affine a⁻¹ 1) (horizontal 1) else 0),
    avg1 (fun a => if a ≠ 0 then b (affine 1 a) (slope a 0) else 0),
    avg1 (fun a => if a ≠ 0 then b (affine a⁻¹ 1) (slope a 0) else 0),
    avg1 (fun c => b W (slope 1 c)),
    avg2 (fun x c => b (affine x (x+c)) (slope 1 c)),
    avg1 (fun c => b (affine 0 c) (vertical 0)),
    avg1 (fun c => b (affine 0 c) (horizontal c)),
    avg1 (fun c => b (affine 1 (1+c)) (vertical 1)),
    avg1 (fun c => b (affine 1 (1+c)) (horizontal (1+c))),
    avg1 (fun c => b (affine 0 c) (slope 1 c)),
    avg1 (fun c => b (affine 1 (1+c)) (slope 1 c)),
    avg3 (fun a c x => b (affine x (a*x+c)) (slope a c))]

def cost (b : Point K 2 → Hyperplane K 2 → ℝ) : ℝ := ∑ i, costTerm b i

theorem costTerm_nonneg {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) (i : Fin 24) : 0 ≤ costTerm b i := by
  classical
  fin_cases i <;> simp only [costTerm]
  all_goals first
    | apply avg1_nonneg; intro x
    | apply avg2_nonneg; intro x y
    | apply avg3_nonneg; intro x y z
  all_goals first
    | exact hb _ _
    | split_ifs <;> first | exact hb _ _ | exact le_refl 0

theorem cost_nonneg {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) : 0 ≤ cost b := by
  exact Finset.sum_nonneg (fun i _ => costTerm_nonneg hb i)

theorem costTerm_le_cost {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) (i : Fin 24) : costTerm b i ≤ cost b := by
  exact Finset.single_le_sum (fun j _ => costTerm_nonneg hb j) (Finset.mem_univ i)

/-- Any set of distinct table entries can be charged together at total cost at most eta. -/
theorem subfamily_le_cost {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) (s : Finset (Fin 24)) :
    ∑ i ∈ s, costTerm b i ≤ cost b := by
  classical
  simpa only [cost] using Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ s) (fun i _ _ => costTerm_nonneg hb i)

theorem avg1_mono {f g : K → ℝ} (h : ∀ x, f x ≤ g x) : avg1 f ≤ avg1 g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (by positivity)

theorem avg2_mono {f g : K → K → ℝ} (h : ∀ x y, f x y ≤ g x y) :
    avg2 f ≤ avg2 g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ =>
    Finset.sum_le_sum (fun y _ => h x y))) (by positivity)

theorem avg3_mono {f g : K → K → K → ℝ} (h : ∀ x y z, f x y z ≤ g x y z) :
    avg3 f ≤ avg3 g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ =>
    Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun z _ => h x y z))))
    (by positivity)

theorem costTerm_mono {b c : Point K 2 → Hyperplane K 2 → ℝ}
    (h : ∀ p H, b p H ≤ c p H) (i : Fin 24) : costTerm b i ≤ costTerm c i := by
  classical
  fin_cases i <;> simp only [costTerm]
  all_goals first
    | apply avg1_mono; intro x
    | apply avg2_mono; intro x y
    | apply avg3_mono; intro x y z
  all_goals first
    | exact h _ _
    | split_ifs <;> first | exact h _ _ | exact le_refl 0

theorem cost_mono {b c : Point K 2 → Hyperplane K 2 → ℝ}
    (h : ∀ p H, b p H ≤ c p H) : cost b ≤ cost c := by
  exact Finset.sum_le_sum (fun i _ => costTerm_mono h i)

private theorem cost_W_on_diagonal (c : K) : Incident (W : Point K 2) (slope 1 c) := by
  simp [W, slope, Incident, Projectivization.orthogonal_mk, dotProduct, Fin.sum_univ_succ]

private theorem avg1_zero {f : K → ℝ} (h : ∀ x, f x = 0) : avg1 f = 0 := by
  simp [avg1, h]
private theorem avg2_zero {f : K → K → ℝ} (h : ∀ x y, f x y = 0) : avg2 f = 0 := by
  simp [avg2, h]
private theorem avg3_zero {f : K → K → K → ℝ} (h : ∀ x y z, f x y z = 0) :
    avg3 f = 0 := by simp [avg3, h]

/-- Every entry samples only original incident flags. This controls all 24 entries,
including the restricted reciprocal family, without an invalid-flag exception. -/
theorem costTerm_zero_of_zero_on_flags {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, Incident p H → b p H = 0) (i : Fin 24) : costTerm b i = 0 := by
  classical
  fin_cases i <;> simp only [costTerm]
  all_goals first
    | apply avg1_zero; intro x
    | apply avg2_zero; intro x y
    | apply avg3_zero; intro x y z
  all_goals try split_ifs with ha
  all_goals first
    | rfl
    | apply hb; simp_all [V_on_vertical, U_on_horizontal, cost_W_on_diagonal]

theorem cost_zero_of_zero_on_flags {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, Incident p H → b p H = 0) : cost b = 0 := by
  exact Finset.sum_eq_zero (fun i _ => costTerm_zero_of_zero_on_flags hb i)

end Erdos85.IncidenceRepair.Plane
