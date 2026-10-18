import Openmath.IncidenceRepair.WeightedPlane
import Openmath.IncidenceRepair.PlaneCostCounting
import Openmath.IncidenceRepair.Pexider

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair.Plane
attribute [local instance] Classical.propDecidable
variable {K L : Type*} [Field K] [Field L] [Fintype K]

def improperX (ψ : Hyperplane K 2 → Hyperplane L 2) (x : K) : ℝ :=
  if ProperX ψ x then 0 else 1
def improperY (ψ : Hyperplane K 2 → Hyperplane L 2) (y : K) : ℝ :=
  if ProperY ψ y then 0 else 1
def productError (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (x y : K) : ℝ :=
  if φ (affine x y) = affine (coordX ψ x) (coordY ψ y) then 0 else 1

theorem improperX_nonneg (ψ : Hyperplane K 2 → Hyperplane L 2) (x : K) :
    0 ≤ improperX ψ x := by unfold improperX; split_ifs <;> norm_num
theorem improperY_nonneg (ψ : Hyperplane K 2 → Hyperplane L 2) (y : K) :
    0 ≤ improperY ψ y := by unfold improperY; split_ifs <;> norm_num
theorem productError_nonneg (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (x y : K) :
    0 ≤ productError φ ψ x y := by unfold productError; split_ifs <;> norm_num

theorem productError_majorant (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (b : Point K 2 → Hyperplane K 2 → ℝ)
    (hb : ∀ p H, 0 ≤ b p H)
    (hbad : ∀ p H, Incident p H → ¬ Incident (φ p) (ψ H) → 1 ≤ b p H)
    (x y : K) :
    productError φ ψ x y ≤ improperX ψ x + improperY ψ y +
      b (affine x y) (vertical x) + b (affine x y) (horizontal y) := by
  have he : productError φ ψ x y ≤ 1 := by unfold productError; split_ifs <;> norm_num
  have hnX := improperX_nonneg ψ x
  have hnY := improperY_nonneg ψ y
  have hvn := hb (affine x y) (vertical x)
  have hhn := hb (affine x y) (horizontal y)
  by_cases hx : ProperX ψ x
  · by_cases hy : ProperY ψ y
    · by_cases hv : Incident (φ (affine x y)) (ψ (vertical x))
      · by_cases hh : Incident (φ (affine x y)) (ψ (horizontal y))
        · have hp := product_of_good_coordinates φ ψ x y hx hy hv hh
          simp only [productError, if_pos hp]
          positivity
        · have heh := hbad (affine x y) (horizontal y) (by simp) hh
          linarith
      · have hev := hbad (affine x y) (vertical x) (by simp) hv
        linarith
    · simp only [improperY, if_neg hy] at hnY ⊢
      linarith
  · simp only [improperX, if_neg hx] at hnX ⊢
    linarith

theorem coordinate_cost_budget (b : Point K 2 → Hyperplane K 2 → ℝ)
    (hb : ∀ p H, 0 ≤ b p H) :
    avg2 (fun x y => b (affine x y) (vertical x) + b (affine x y) (horizontal y)) ≤ cost b := by
  have h := subfamily_le_cost hb ({2,3} : Finset (Fin 24))
  simpa [costTerm, Finset.sum_insert, Finset.sum_singleton, avg2_add] using h

/-- Actual product exceptions satisfy (2.8). The support deficits are supplied
by the separate support theorem, not assumed by the final plane theorem. -/
theorem product_budget (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (b : Point K 2 → Hyperplane K 2 → ℝ)
    (hb : ∀ p H, 0 ≤ b p H)
    (hbad : ∀ p H, Incident p H → ¬ Incident (φ p) (ψ H) → 1 ≤ b p H)
    (hX : count (fun x => ¬ ProperX ψ x) ≤ 17 * cost b * Fintype.card K)
    (hY : count (fun y => ¬ ProperY ψ y) ≤ 17 * cost b * Fintype.card K) :
    ∑ x, ∑ y, productError φ ψ x y ≤ 35 * cost b * (Fintype.card K : ℝ)^2 := by
  have hmaj := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun y _ => productError_majorant φ ψ b hb hbad x y))
  have hcost := sum_le_of_avg2_le (coordinate_cost_budget b hb)
  have hx : ∑ x, improperX ψ x = count (fun x => ¬ ProperX ψ x) := by
    unfold count
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : ProperX ψ x <;> simp [improperX, h]
  have hy : ∑ y, improperY ψ y = count (fun y => ¬ ProperY ψ y) := by
    unfold count
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : ProperY ψ y <;> simp [improperY, h]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul, hx, hy] at hmaj
  simp only [Finset.sum_add_distrib] at hcost
  have hq : (0:ℝ) ≤ Fintype.card K := by positivity
  have hxq := mul_le_mul_of_nonneg_right hX hq
  have hyq := mul_le_mul_of_nonneg_right hY hq
  nlinarith

private theorem W_on_diagonal (c : K) : Incident (W : Point K 2) (slope 1 c) := by
  simp [W, slope, Incident, Projectivization.orthogonal_mk, dotProduct, Fin.sum_univ_succ]

theorem pexider_error_majorant (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hbad : ∀ p H, Incident p H → ¬ Incident (φ p) (ψ H) → 1 ≤ b p H)
    (u c : K) :
    Pexider.error (coordX ψ) (coordY ψ) (diagonalIntercept ψ) u c ≤
      productError φ ψ u (u+c) + b W (slope 1 c) + b (affine u (u+c)) (slope 1 c) := by
  have he : Pexider.error (coordX ψ) (coordY ψ) (diagonalIntercept ψ) u c ≤ 1 := by
    unfold Pexider.error; split_ifs <;> norm_num
  have hn := productError_nonneg φ ψ u (u+c)
  have hw := hb W (slope 1 c)
  have hf := hb (affine u (u+c)) (slope 1 c)
  by_cases hprod : φ (affine u (u+c)) = affine (coordX ψ u) (coordY ψ (u+c))
  · by_cases hW : Incident (φ W) (ψ (slope 1 c))
    · by_cases hflag : Incident (φ (affine u (u+c))) (ψ (slope 1 c))
      · have hh := pexider_of_product_and_flags φ ψ hp u c hprod hW hflag
        simp only [Pexider.error, if_pos hh]
        positivity
      · have hbf := hbad (affine u (u+c)) (slope 1 c) (by simp) hflag
        linarith
    · have hbw := hbad W (slope 1 c) (W_on_diagonal c) hW
      linarith
  · simp only [productError, if_neg hprod]
    linarith

private theorem avg2_ignore_first (f : K → ℝ) : avg2 (fun _ y => f y) = avg1 f := by
  have hq : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg2, avg1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem pexider_extra_cost_budget (b : Point K 2 → Hyperplane K 2 → ℝ)
    (hb : ∀ p H, 0 ≤ b p H) :
    avg2 (fun u c => b W (slope 1 c) + b (affine u (u+c)) (slope 1 c)) ≤ cost b := by
  have h := subfamily_le_cost hb ({15,16} : Finset (Fin 24))
  simpa [costTerm, Finset.sum_insert, Finset.sum_singleton, avg2_add, avg2_ignore_first] using h

/-- Actual Pexider failure count (2.9), with original diagonal flags charged. -/
theorem pexider_budget (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hbad : ∀ p H, Incident p H → ¬ Incident (φ p) (ψ H) → 1 ≤ b p H)
    (hX : count (fun x => ¬ ProperX ψ x) ≤ 17 * cost b * Fintype.card K)
    (hY : count (fun y => ¬ ProperY ψ y) ≤ 17 * cost b * Fintype.card K) :
    Pexider.errorCount (coordX ψ) (coordY ψ) (diagonalIntercept ψ) ≤
      (36 * cost b) * (Fintype.card K : ℝ)^2 := by
  have hmaj := Finset.sum_le_sum (s := Finset.univ) (fun u _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun c _ => pexider_error_majorant φ ψ hp b hb hbad u c))
  have hprod := product_budget φ ψ b hb hbad hX hY
  have hextra := sum_le_of_avg2_le (pexider_extra_cost_budget b hb)
  have hshift : (∑ u : K, ∑ c : K, productError φ ψ u (u+c)) =
      ∑ u : K, ∑ y : K, productError φ ψ u y := by
    apply Finset.sum_congr rfl
    intro u hu
    exact Pexider.sum_add_left u (productError φ ψ u)
  simp only [Finset.sum_add_distrib] at hmaj hextra
  rw [hshift] at hmaj
  change Pexider.errorCount (coordX ψ) (coordY ψ) (diagonalIntercept ψ) ≤ _ at hmaj
  linarith

theorem fixed_extra_cost_budget (b : Point K 2 → Hyperplane K 2 → ℝ)
    (hb : ∀ p H, 0 ≤ b p H) (i : K) (hi : i=0 ∨ i=1) :
    avg1 (fun c => b (affine i (i+c)) (vertical i) +
      b (affine i (i+c)) (horizontal (i+c)) + b W (slope 1 c) +
      b (affine i (i+c)) (slope 1 c)) ≤ cost b := by
  rcases hi with rfl | rfl
  · have h := subfamily_le_cost hb ({15,17,18,21} : Finset (Fin 24))
    simpa [costTerm, Finset.sum_insert, Finset.sum_singleton, avg1_add,
      add_assoc, add_comm, add_left_comm] using h
  · have h := subfamily_le_cost hb ({15,19,20,22} : Finset (Fin 24))
    simpa [costTerm, Finset.sum_insert, Finset.sum_singleton, avg1_add,
      add_assoc, add_comm, add_left_comm] using h

/-- The fixed protected columns use their own table entries, not a global average. -/
theorem fixed_row_budget (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hbad : ∀ p H, Incident p H → ¬ Incident (φ p) (ψ H) → 1 ≤ b p H)
    (hY : count (fun y => ¬ ProperY ψ y) ≤ 17 * cost b * Fintype.card K)
    (i : K) (hi : i=0 ∨ i=1) :
    count (fun c => coordY ψ (i+c) ≠ coordX ψ i + diagonalIntercept ψ c) ≤
      20 * cost b * Fintype.card K := by
  have hproper : ProperX ψ i := by
    rcases hi with rfl | rfl
    · exact (protected_values φ ψ hp).1
    · exact (protected_values φ ψ hp).2.1
  have hpoint : ∀ c : K,
      Pexider.error (coordX ψ) (coordY ψ) (diagonalIntercept ψ) i c ≤
        improperY ψ (i+c) + b (affine i (i+c)) (vertical i) +
        b (affine i (i+c)) (horizontal (i+c)) + b W (slope 1 c) +
        b (affine i (i+c)) (slope 1 c) := by
    intro c
    have hh := productError_majorant φ ψ b hb hbad i (i+c)
    simp only [improperX, if_pos hproper, zero_add] at hh
    linarith [pexider_error_majorant φ ψ hp b hb hbad i c]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hpoint c)
  have hc := sum_le_of_avg1_le (fixed_extra_cost_budget b hb i hi)
  have hy : (∑ c : K, improperY ψ (i+c)) = count (fun y => ¬ ProperY ψ y) := by
    rw [Pexider.sum_add_left]
    unfold count
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : ProperY ψ y <;> simp [improperY, h]
  have herr : count (fun c => coordY ψ (i+c) ≠ coordX ψ i + diagonalIntercept ψ c) =
      ∑ c, Pexider.error (coordX ψ) (coordY ψ) (diagonalIntercept ψ) i c := by
    unfold count
    apply Finset.sum_congr rfl
    intro c hc
    by_cases h : coordY ψ (i+c) = coordX ψ i + diagonalIntercept ψ c <;>
      simp [Pexider.error, h]
  simp only [Finset.sum_add_distrib] at hs hc
  rw [hy] at hs
  rw [herr]
  have hn : 0 ≤ cost b * Fintype.card K := mul_nonneg (cost_nonneg hb) (by positivity)
  linarith

theorem diagonal_error_majorant (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hbad : ∀ p H, Incident p H → ¬ Incident (φ p) (ψ H) → 1 ≤ b p H)
    (t : K) :
    (if coordY ψ t ≠ coordX ψ t then (1:ℝ) else 0) ≤
      improperX ψ t + improperY ψ t + b (affine t t) (vertical t) +
      b (affine t t) (horizontal t) + b (affine t t) (slope 1 0) := by
  have hnX := improperX_nonneg ψ t
  have hnY := improperY_nonneg ψ t
  have hvn := hb (affine t t) (vertical t)
  have hhn := hb (affine t t) (horizontal t)
  have hdn := hb (affine t t) (slope 1 0)
  by_cases he : coordY ψ t = coordX ψ t
  · simp only [he, ne_eq, not_true_eq_false, if_false]
    positivity
  · simp only [he, ne_eq, not_false_eq_true, if_true]
    by_cases hx : ProperX ψ t
    · by_cases hy : ProperY ψ t
      · by_cases hv : Incident (φ (affine t t)) (ψ (vertical t))
        · by_cases hh : Incident (φ (affine t t)) (ψ (horizontal t))
          · by_cases hd : Incident (φ (affine t t)) (ψ (slope 1 0))
            · exact False.elim (he (equal_coordinates_of_diagonal φ ψ hp t hx hy hv hh hd))
            · have hbd := hbad (affine t t) (slope 1 0) (by simp) hd
              linarith
          · have hbh := hbad (affine t t) (horizontal t) (by simp) hh
            linarith
        · have hbv := hbad (affine t t) (vertical t) (by simp) hv
          linarith
      · simp only [improperY, if_neg hy]
        linarith
    · simp only [improperX, if_neg hx]
      linarith

theorem diagonal_extra_cost_budget (b : Point K 2 → Hyperplane K 2 → ℝ)
    (hb : ∀ p H, 0 ≤ b p H) :
    avg1 (fun t => b (affine t t) (vertical t) + b (affine t t) (horizontal t) +
      b (affine t t) (slope 1 0)) ≤ cost b := by
  have h := subfamily_le_cost hb ({4,5,6} : Finset (Fin 24))
  simpa [costTerm, Finset.sum_insert, Finset.sum_singleton, avg1_add, add_assoc] using h

/-- Actual diagonal disagreement bound (2.11). -/
theorem diagonal_budget (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hbad : ∀ p H, Incident p H → ¬ Incident (φ p) (ψ H) → 1 ≤ b p H)
    (hX : count (fun x => ¬ ProperX ψ x) ≤ 17 * cost b * Fintype.card K)
    (hY : count (fun y => ¬ ProperY ψ y) ≤ 17 * cost b * Fintype.card K) :
    count (fun t => coordY ψ t ≠ coordX ψ t) ≤ 36 * cost b * Fintype.card K := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun t _ =>
    diagonal_error_majorant φ ψ hp b hb hbad t)
  have hc := sum_le_of_avg1_le (diagonal_extra_cost_budget b hb)
  have hx : ∑ t, improperX ψ t = count (fun t => ¬ ProperX ψ t) := by
    unfold count
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : ProperX ψ x <;> simp [improperX, h]
  have hy : ∑ t, improperY ψ t = count (fun t => ¬ ProperY ψ t) := by
    unfold count
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : ProperY ψ y <;> simp [improperY, h]
  simp only [Finset.sum_add_distrib] at hs hc
  rw [hx,hy] at hs
  have herr : count (fun t => coordY ψ t ≠ coordX ψ t) =
      ∑ t : K, if coordY ψ t ≠ coordX ψ t then (1:ℝ) else 0 := by
    unfold count
    apply Finset.sum_congr rfl
    intro t ht
    by_cases h : coordY ψ t = coordX ψ t <;> simp [h]
  rw [herr]
  have hn : 0 ≤ cost b * Fintype.card K := mul_nonneg (cost_nonneg hb) (by positivity)
  linarith

/-- All four actual budgets required by the protected Pexider correction. -/
theorem pexider_budgets (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hbad : ∀ p H, Incident p H → ¬ Incident (φ p) (ψ H) → 1 ≤ b p H)
    (hX : count (fun x => ¬ ProperX ψ x) ≤ 17 * cost b * Fintype.card K)
    (hY : count (fun y => ¬ ProperY ψ y) ≤ 17 * cost b * Fintype.card K) :
    (∑ x, ∑ y, productError φ ψ x y ≤ 35 * cost b * (Fintype.card K : ℝ)^2) ∧
    Pexider.errorCount (coordX ψ) (coordY ψ) (diagonalIntercept ψ) ≤
      (36 * cost b) * (Fintype.card K : ℝ)^2 ∧
    (∀ i : K, i=0 ∨ i=1 →
      count (fun c => coordY ψ (i+c) ≠ coordX ψ i + diagonalIntercept ψ c) ≤
        20 * cost b * Fintype.card K) ∧
    count (fun t => coordY ψ t ≠ coordX ψ t) ≤ 36 * cost b * Fintype.card K :=
  ⟨product_budget φ ψ b hb hbad hX hY,
   pexider_budget φ ψ hp b hb hbad hX hY,
   fixed_row_budget φ ψ hp b hb hbad hY,
   diagonal_budget φ ψ hp b hb hbad hX hY⟩

end Erdos85.IncidenceRepair.Plane
