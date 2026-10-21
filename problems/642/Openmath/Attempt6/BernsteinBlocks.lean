import Openmath.Attempt6.AbsorberSelection

/-! Finite independent bounded-block Bernstein estimates. The probability
law is the explicit product of the supplied finite block distributions.
The variance proxy is a sum of block second moments, never a block count.
-/
namespace Erdos585.Attempt6.BernsteinBlocks
noncomputable section
open scoped BigOperators
open AbsorberSelection.ProductLaw
variable {J B : Type*} [Fintype J] [DecidableEq J] [Fintype B]

def mean (w X : B → ℝ) : ℝ := ∑ z, w z * X z
def variance (w X : B → ℝ) : ℝ := ∑ z, w z * (X z - mean w X) ^ 2

theorem exp_quadratic {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := (le_abs_self (Real.exp x - 1 - x)).trans (Real.abs_exp_sub_one_sub_id_le hx)
  linarith

/-- A centered finite block has a variance-sensitive local MGF bound. -/
theorem centered_block_mgf (w Y : B → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hs : ∑ z, w z = 1) (hc : ∑ z, w z * Y z = 0)
    (b t : ℝ) (ht : 0 ≤ t) (htb : t * b ≤ 1) (hY : ∀ z, |Y z| ≤ b) :
    (∑ z, w z * Real.exp (t * Y z)) ≤ Real.exp (t ^ 2 * ∑ z, w z * Y z ^ 2) := by
  have he (z) : Real.exp (t * Y z) ≤ 1 + t * Y z + (t * Y z) ^ 2 := by
    apply exp_quadratic
    rw [abs_mul, abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_left (hY z) ht).trans htb
  calc
    _ ≤ ∑ z, w z * (1 + t * Y z + (t * Y z) ^ 2) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (he z) (hw z)
    _ = 1 + t ^ 2 * ∑ z, w z * Y z ^ 2 := by
      simp only [mul_add, mul_one, mul_pow]
      simp_rw [show ∀ z, w z * (t * Y z) = t * (w z * Y z) from fun z => by ring,
        show ∀ z, w z * (t ^ 2 * Y z ^ 2) = t ^ 2 * (w z * Y z ^ 2) from fun z => by ring]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hs, hc]
      ring
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (t ^ 2 * ∑ z, w z * Y z ^ 2)

/-- Independence is obtained from the explicit finite product mass. -/
theorem centered_product_mgf (w Y : J → B → ℝ) (hw : ∀ j z, 0 ≤ w j z)
    (hs : ∀ j, ∑ z, w j z = 1) (hc : ∀ j, ∑ z, w j z * Y j z = 0)
    (b t V : ℝ) (ht : 0 ≤ t) (htb : t * b ≤ 1)
    (hY : ∀ j z, |Y j z| ≤ b) (hV : (∑ j, ∑ z, w j z * Y j z ^ 2) ≤ V) :
    (∑ ω : J → B, mass w ω * Real.exp (t * ∑ j, Y j (ω j))) ≤ Real.exp (t ^ 2 * V) := by
  rw [exp_factorization]
  calc
    _ ≤ ∏ j, Real.exp (t ^ 2 * ∑ z, w j z * Y j z ^ 2) := by
      apply Finset.prod_le_prod
      · intro j _; exact Finset.sum_nonneg fun z _ => mul_nonneg (hw j z) (Real.exp_pos _).le
      · intro j _; exact centered_block_mgf (w j) (Y j) (hw j) (hs j) (hc j) b t ht htb (hY j)
    _ = Real.exp (t ^ 2 * ∑ j, ∑ z, w j z * Y j z ^ 2) := by rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hV (sq_nonneg t))

/-- Bernstein upper tail with a variance proxy and universal constants.
The restricted MGF window gives denominator4V+2bu. -/
theorem centered_upper_tail (w Y : J → B → ℝ) (hw : ∀ j z, 0 ≤ w j z)
    (hs : ∀ j, ∑ z, w j z = 1) (hc : ∀ j, ∑ z, w j z * Y j z = 0)
    (b V u : ℝ) (hb : 0 < b) (hu : 0 < u)
    (hY : ∀ j z, |Y j z| ≤ b) (hV : (∑ j, ∑ z, w j z * Y j z ^ 2) ≤ V) :
    (∑ ω : J → B, if u ≤ ∑ j, Y j (ω j) then mass w ω else 0) ≤
      Real.exp (-(u ^ 2 / (4 * V + 2 * b * u))) := by
  have hV0 : 0 ≤ V := le_trans (Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun z _ => mul_nonneg (hw j z) (sq_nonneg _)) hV
  let D := 2 * V + b * u
  have hD : 0 < D := by dsimp [D]; positivity
  let t := u / D
  have ht : 0 ≤ t := (div_pos hu hD).le
  have htb : t * b ≤ 1 := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_le_one hD).mpr
    dsimp [D]
    nlinarith
  have hVt : V * t ≤ u / 2 := by
    dsimp [t]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hD).mpr
    dsimp [D]
    nlinarith [mul_pos hb hu, sq_nonneg u]
  have he : V * t ^ 2 - t * u ≤ -(t * u / 2) := by
    have h := mul_le_mul_of_nonneg_right hVt ht
    nlinarith
  calc
    _ ≤ (∑ ω : J → B, mass w ω * Real.exp (t * ∑ j, Y j (ω j))) /
        Real.exp (t * u) := exp_tail (mass w) (fun ω => ∑ j, Y j (ω j)) (nonneg w hw) t u ht
    _ ≤ Real.exp (t ^ 2 * V) / Real.exp (t * u) :=
      div_le_div_of_nonneg_right (centered_product_mgf w Y hw hs hc b t V ht htb hY hV) (Real.exp_pos _).le
    _ = Real.exp (V * t ^ 2 - t * u) := by rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(t * u / 2)) := Real.exp_le_exp.mpr he
    _ = _ := by
      congr 1
      dsimp [t, D]
      field_simp
      <;> ring

/-- The complete two-sided Bernstein bound for actual independent finite
blocks. Centering and boundedness are blockwise; no column independence is
postulated. -/
theorem centered_two_sided_tail (w Y : J → B → ℝ) (hw : ∀ j z, 0 ≤ w j z)
    (hs : ∀ j, ∑ z, w j z = 1) (hc : ∀ j, ∑ z, w j z * Y j z = 0)
    (b V u : ℝ) (hb : 0 < b) (hu : 0 < u)
    (hY : ∀ j z, |Y j z| ≤ b) (hV : (∑ j, ∑ z, w j z * Y j z ^ 2) ≤ V) :
    (∑ ω : J → B, if u ≤ |∑ j, Y j (ω j)| then mass w ω else 0) ≤
      2 * Real.exp (-(u ^ 2 / (4 * V + 2 * b * u))) := by
  have hl := centered_upper_tail w (fun j z => -Y j z) hw hs
    (fun j => by simp only [mul_neg]; rw [Finset.sum_neg_distrib, hc, neg_zero])
    b V u hb hu (fun j z => by simpa using hY j z)
    (by simpa only [neg_sq] using hV)
  have hr := centered_upper_tail w Y hw hs hc b V u hb hu hY hV
  calc
    _ ≤ (∑ ω : J → B, if u ≤ ∑ j, Y j (ω j) then mass w ω else 0) +
        ∑ ω : J → B, if u ≤ ∑ j, -Y j (ω j) then mass w ω else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro ω _
      have hn := nonneg w hw ω
      have hneg : (∑ j, -Y j (ω j)) = -(∑ j, Y j (ω j)) := by rw [Finset.sum_neg_distrib]
      rw [hneg]
      by_cases hsign : 0 ≤ ∑ j, Y j (ω j)
      · rw [abs_of_nonneg hsign]
        split_ifs <;> simp_all <;> linarith
      · rw [abs_of_neg (lt_of_not_ge hsign)]
        split_ifs <;> simp_all <;> linarith
    _ ≤ _ := by linarith

/-- Square-root Bernstein form, with fixed universal constants2 and2. -/
theorem centered_bernstein (w Y : J → B → ℝ) (hw : ∀ j z, 0 ≤ w j z)
    (hs : ∀ j, ∑ z, w j z = 1) (hc : ∀ j, ∑ z, w j z * Y j z = 0)
    (b V a : ℝ) (hb : 0 < b) (ha : 0 < a)
    (hY : ∀ j z, |Y j z| ≤ b) (hV : (∑ j, ∑ z, w j z * Y j z ^ 2) ≤ V) :
    (∑ ω : J → B, if 2 * Real.sqrt (V * a) + 2 * b * a ≤ |∑ j, Y j (ω j)|
      then mass w ω else 0) ≤ 2 * Real.exp (-a) := by
  have hV0 : 0 ≤ V := le_trans (Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun z _ => mul_nonneg (hw j z) (sq_nonneg _)) hV
  let u := 2 * Real.sqrt (V * a) + 2 * b * a
  have hu : 0 < u := by dsimp [u]; positivity
  have hden : 0 < 4 * V + 2 * b * u := by positivity
  have hroot := Real.sq_sqrt (mul_nonneg hV0 ha.le)
  have hroot0 := Real.sqrt_nonneg (V * a)
  have hquad : a * (4 * V + 2 * b * u) ≤ u ^ 2 := by
    dsimp [u]
    nlinarith [mul_nonneg (mul_nonneg hb.le ha.le) hroot0]
  have hfrac : a ≤ u ^ 2 / (4 * V + 2 * b * u) := (le_div_iff₀ hden).mpr hquad
  exact (centered_two_sided_tail w Y hw hs hc b V u hb hu hY hV).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hfrac)) (by norm_num))

theorem mean_mem_interval (w X : B → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hs : ∑ z, w z = 1) (b : ℝ) (hX : ∀ z, 0 ≤ X z ∧ X z ≤ b) :
    0 ≤ mean w X ∧ mean w X ≤ b := by
  refine ⟨Finset.sum_nonneg fun z _ => mul_nonneg (hw z) (hX z).1, ?_⟩
  calc
    _ ≤ ∑ z, w z * b := Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hX z).2 (hw z)
    _ = b := by rw [← Finset.sum_mul, hs, one_mul]

theorem centered_mean_zero (w X : B → ℝ) (hs : ∑ z, w z = 1) :
    (∑ z, w z * (X z - mean w X)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
  dsimp [mean]
  ring

theorem centered_abs_le (w X : B → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hs : ∑ z, w z = 1) (b : ℝ) (hX : ∀ z, 0 ≤ X z ∧ X z ≤ b) :
    ∀ z, |X z - mean w X| ≤ b := by
  intro z
  have hm := mean_mem_interval w X hw hs b hX
  rw [abs_le]
  constructor <;> linarith [(hX z).1, (hX z).2]

/-- The exact variance identity and nonnegative-block bound charge the
actual expected load, irrespective of how many blocks there are. -/
theorem variance_le_bound_mul_mean (w X : B → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hs : ∑ z, w z = 1) (b : ℝ) (hX : ∀ z, 0 ≤ X z ∧ X z ≤ b) :
    variance w X ≤ b * mean w X := by
  have hid : variance w X = (∑ z, w z * X z ^ 2) - (mean w X) ^ 2 := by
    dsimp [variance]
    simp_rw [show ∀ z, w z * (X z - mean w X) ^ 2 =
      w z * X z ^ 2 - (2 * mean w X) * (w z * X z) + (mean w X) ^ 2 * w z from fun z => by ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hs]
    change (∑ z, w z * X z ^ 2) - 2 * mean w X * mean w X + (mean w X) ^ 2 * 1 = _
    ring
  have hsq : (∑ z, w z * X z ^ 2) ≤ b * mean w X := by
    calc
      _ ≤ ∑ z, w z * (b * X z) := by
        apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_left _ (hw z)
        nlinarith [(hX z).1, (hX z).2]
      _ = _ := by dsimp [mean]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
  rw [hid]
  nlinarith [sq_nonneg (mean w X)]

/-- Nonnegative block concentration with variance proxy b times total mean.
No dependence on the number of blocks is introduced. -/
theorem nonnegative_block_bernstein (w X : J → B → ℝ) (hw : ∀ j z, 0 ≤ w j z)
    (hs : ∀ j, ∑ z, w j z = 1) (b a : ℝ) (hb : 0 < b) (ha : 0 < a)
    (hX : ∀ j z, 0 ≤ X j z ∧ X j z ≤ b) :
    let μ := ∑ j, mean (w j) (X j)
    (∑ ω : J → B, if 2 * Real.sqrt (b * μ * a) + 2 * b * a ≤
      |(∑ j, X j (ω j)) - μ| then mass w ω else 0) ≤ 2 * Real.exp (-a) := by
  dsimp only
  let Y : J → B → ℝ := fun j z => X j z - mean (w j) (X j)
  have hV : (∑ j, ∑ z, w j z * Y j z ^ 2) ≤ b * ∑ j, mean (w j) (X j) := by
    calc
      _ = ∑ j, variance (w j) (X j) := rfl
      _ ≤ ∑ j, b * mean (w j) (X j) := Finset.sum_le_sum fun j _ =>
        variance_le_bound_mul_mean (w j) (X j) (hw j) (hs j) b (hX j)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have h := centered_bernstein w Y hw hs
    (fun j => centered_mean_zero (w j) (X j) (hs j))
    b (b * ∑ j, mean (w j) (X j)) a hb ha
    (fun j => centered_abs_le (w j) (X j) (hw j) (hs j) b (hX j)) hV
  simpa only [Y, Finset.sum_sub_distrib] using h

                                                                         
                                                                      
theorem two_coordinate_expectation (w : J → B → ℝ) (hs : ∀ j, ∑ z, w j z = 1)
    (i k : J) (hik : i ≠ k) (f g : B → ℝ) :
    (∑ ω : J → B, mass w ω * (f (ω i) * g (ω k))) =
      mean (w i) f * mean (w k) g := by
  let F : J → B → ℝ := fun j z => (if j = i then f z else 1) * (if j = k then g z else 1)
  have h := factorization w F
  have hl (ω : J → B) : (∏ j, F j (ω j)) = f (ω i) * g (ω k) := by
    dsimp [F]
    rw [Finset.prod_mul_distrib]
    simp
  have hr (j : J) : (∑ z, w j z * F j z) =
      (if j = i then mean (w i) f else 1) * (if j = k then mean (w k) g else 1) := by
    by_cases hi : j = i <;> by_cases hk : j = k <;> simp_all [F, mean]
  simp_rw [hl, hr] at h
  rw [Finset.prod_mul_distrib] at h
  simpa using h

theorem centered_total_second_moment (w Y : J → B → ℝ)
    (hs : ∀ j, ∑ z, w j z = 1) (hc : ∀ j, ∑ z, w j z * Y j z = 0) :
    (∑ ω : J → B, mass w ω * (∑ j, Y j (ω j)) ^ 2) =
      ∑ j, ∑ z, w j z * Y j z ^ 2 := by
  have hcross (i k : J) :
      (∑ ω : J → B, mass w ω * (Y i (ω i) * Y k (ω k))) =
        if k = i then ∑ z, w i z * Y i z ^ 2 else 0 := by
    by_cases hki : k = i
    · subst k
      simpa only [if_true, ← pow_two] using coordinate_expectation w hs i (fun z => Y i z ^ 2)
    · rw [if_neg hki, two_coordinate_expectation w hs i k (Ne.symm hki)]
      simp [mean, hc]
  calc
    _ = ∑ i, ∑ k, ∑ ω : J → B, mass w ω * (Y i (ω i) * Y k (ω k)) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = _ := by simp_rw [hcross]; simp

/-- The actual variance of the independent block sum is the sum of the
actual block variances. This is derived from the explicit product law. -/
theorem product_variance_identity (w X : J → B → ℝ)
    (hs : ∀ j, ∑ z, w j z = 1) :
    variance (mass w) (fun ω : J → B => ∑ j, X j (ω j)) =
      ∑ j, variance (w j) (X j) := by
  have hm : mean (mass w) (fun ω : J → B => ∑ j, X j (ω j)) =
      ∑ j, mean (w j) (X j) := total_expectation w X hs
  dsimp only [variance]
  rw [hm]
  simp_rw [← Finset.sum_sub_distrib]
  exact centered_total_second_moment w (fun j z => X j z - mean (w j) (X j)) hs
    (fun j => centered_mean_zero (w j) (X j) (hs j))

/-- The variance of the full sum is bounded by b times its total expectation,
without any term involving the total number of blocks. -/
theorem product_variance_le_bound_mul_total_mean (w X : J → B → ℝ)
    (hw : ∀ j z, 0 ≤ w j z) (hs : ∀ j, ∑ z, w j z = 1)
    (b : ℝ) (hX : ∀ j z, 0 ≤ X j z ∧ X j z ≤ b) :
    variance (mass w) (fun ω : J → B => ∑ j, X j (ω j)) ≤
      b * ∑ j, mean (w j) (X j) := by
  rw [product_variance_identity w X hs, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => variance_le_bound_mul_mean (w j) (X j) (hw j) (hs j) b (hX j)

/-- The centered Bernstein statement may use the actual variance of the
full product-law sum as its input, rather than block second moments. -/
theorem centered_bernstein_of_variance_le (w Y : J → B → ℝ)
    (hw : ∀ j z, 0 ≤ w j z) (hs : ∀ j, ∑ z, w j z = 1)
    (hc : ∀ j, ∑ z, w j z * Y j z = 0)
    (b V a : ℝ) (hb : 0 < b) (ha : 0 < a)
    (hY : ∀ j z, |Y j z| ≤ b)
    (hV : variance (mass w) (fun ω : J → B => ∑ j, Y j (ω j)) ≤ V) :
    (∑ ω : J → B, if 2 * Real.sqrt (V * a) + 2 * b * a ≤ |∑ j, Y j (ω j)|
      then mass w ω else 0) ≤ 2 * Real.exp (-a) := by
  have hid : variance (mass w) (fun ω : J → B => ∑ j, Y j (ω j)) =
      ∑ j, ∑ z, w j z * Y j z ^ 2 := by
    rw [product_variance_identity]
    · simp [variance, mean, hc]
    · exact hs
  rw [hid] at hV
  exact centered_bernstein w Y hw hs hc b V a hb ha hY hV

end
end Erdos585.Attempt6.BernsteinBlocks
