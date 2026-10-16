import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.FiniteCoarea

/-! An actual finite weighted median and the full mean-zero Rayleigh inequality.
The median is constructed from cumulative weights, not supplied as a premise. -/
namespace Erdos642.CampaignFe72210bContinuation3.WeightedMedian

open scoped BigOperators
open FiniteCoarea
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A genuine finite weighted median, including zero-weight ties. -/
theorem exists_weighted_median [Nonempty V] (μ : V → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (f : V → ℝ) : ∃ m : ℝ,
      (∑ x, if f x < m then μ x else 0) ≤ (∑ x, μ x) / 2 ∧
      (∑ x, if m < f x then μ x else 0) ≤ (∑ x, μ x) / 2 := by
  classical
  let W := ∑ x, μ x
  let L := fun a : ℝ => ∑ x, if f x ≤ a then μ x else 0
  let C := Finset.univ.filter fun x => W / 2 ≤ L (f x)
  have hW : 0 ≤ W := Finset.sum_nonneg fun x _ => hμ x
  have hC : C.Nonempty := by
    obtain ⟨z, _, hz⟩ := Finset.exists_max_image (Finset.univ : Finset V) f
      Finset.univ_nonempty
    refine ⟨z, ?_⟩
    have hL : L (f z) = W := by simp [L, W, hz]
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hL]
    linarith
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image C f hC
  have hhalf : W / 2 ≤ L (f z) := (Finset.mem_filter.mp hz).2
  refine ⟨f z, ?_, ?_⟩
  · let T := Finset.univ.filter fun x => f x < f z
    by_cases hT : T.Nonempty
    · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image T f hT
      have haz : f a < f z := (Finset.mem_filter.mp ha).2
      have hnot : a ∉ C := by
        intro hac
        exact (not_le_of_gt haz) (hmin a hac)
      have hLa : L (f a) < W / 2 := by
        have hn : ¬ W / 2 ≤ L (f a) := by simpa [C] using hnot
        exact lt_of_not_ge hn
      have heq : (∑ x, if f x < f z then μ x else 0) = L (f a) := by
        apply Finset.sum_congr rfl
        intro x _
        have hx : f x < f z ↔ f x ≤ f a := by
          constructor
          · intro hx
            exact hmax x (by simp [T, hx])
          · intro hx
            exact lt_of_le_of_lt hx haz
        simp only [hx]
      rw [heq]
      exact hLa.le
    · have hempty : (∑ x, if f x < f z then μ x else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        have hx : ¬ f x < f z := by
          intro hx
          exact hT ⟨x, by simp [T, hx]⟩
        simp [hx]
      rw [hempty]
      exact div_nonneg hW (by norm_num)
  · have hpart : L (f z) + (∑ x, if f z < f x then μ x else 0) = W := by
      dsimp only [L, W]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : f x ≤ f z
      · simp [hx, not_lt_of_ge hx]
      · simp [hx, lt_of_not_ge hx]
    change _ ≤ W / 2
    linarith

noncomputable def positivePart (f : V → ℝ) (m : ℝ) (x : V) : ℝ := max (f x - m) 0
noncomputable def negativePart (f : V → ℝ) (m : ℝ) (x : V) : ℝ := max (m - f x) 0

private theorem parts_sq (a : ℝ) : (max a 0)^2 + (max (-a) 0)^2 = a^2 := by
  by_cases ha : 0 ≤ a
  · simp [max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    simp [max_eq_right ha', max_eq_left (neg_nonneg.mpr ha')]

private theorem parts_difference_sq (a b : ℝ) :
    (max a 0 - max b 0)^2 + (max (-a) 0 - max (-b) 0)^2 ≤ (a - b)^2 := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · simp [max_eq_left ha, max_eq_left hb,
      max_eq_right (neg_nonpos.mpr ha), max_eq_right (neg_nonpos.mpr hb)]
  · have hb' : b ≤ 0 := le_of_not_ge hb
    simp only [max_eq_left ha, max_eq_right hb',
      max_eq_right (neg_nonpos.mpr ha), max_eq_left (neg_nonneg.mpr hb')]
    nlinarith [mul_nonneg ha (neg_nonneg.mpr hb')]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    simp only [max_eq_right ha', max_eq_left hb,
      max_eq_left (neg_nonneg.mpr ha'), max_eq_right (neg_nonpos.mpr hb)]
    nlinarith [mul_nonneg (neg_nonneg.mpr ha') hb]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    have hb' : b ≤ 0 := le_of_not_ge hb
    simp only [max_eq_right ha', max_eq_right hb',
      max_eq_left (neg_nonneg.mpr ha'), max_eq_left (neg_nonneg.mpr hb')]
    nlinarith

omit [DecidableEq V] in
/-- Actual energy splits into the two positive parts with the correct inequality. -/
theorem energy_parts_le (w : V → V → ℝ) (hw : ∀ x y, 0 ≤ w x y)
    (f : V → ℝ) (m : ℝ) :
    energy w (positivePart f m) + energy w (negativePart f m) ≤ energy w f := by
  have hpoint (x y : V) :
      w x y * (positivePart f m x - positivePart f m y)^2 +
      w x y * (negativePart f m x - negativePart f m y)^2 ≤
      w x y * (f x - f y)^2 := by
    have hp := parts_difference_sq (f x - m) (f y - m)
    have hneg (x : V) : -(f x - m) = m - f x := by ring
    simp only [hneg] at hp
    have hd : (f x - m) - (f y - m) = f x - f y := by ring
    rw [hd] at hp
    have hm := mul_le_mul_of_nonneg_left hp (hw x y)
    simpa [positivePart, negativePart, mul_add] using hm
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (fun x _ => Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun y _ => hpoint x y))
  simp only [Finset.sum_add_distrib] at hsum
  unfold energy
  linarith

omit [DecidableEq V] in
/-- Exact squared norm identity, without a mean-zero premise. -/
theorem normSq_parts (w : V → V → ℝ) (f : V → ℝ) (m : ℝ) :
    normSq w (positivePart f m) + normSq w (negativePart f m) =
      normSq w (fun x => f x - m) := by
  unfold normSq mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hp := parts_sq (f x - m)
  have hneg : -(f x - m) = m - f x := by ring
  rw [hneg] at hp
  simpa [positivePart, negativePart, ← mul_add] using congrArg (row w x * ·) hp

omit [DecidableEq V] in
/-- The shifted norm is at least the original norm at weighted mean zero. -/
theorem normSq_shift_mean_zero (w : V → V → ℝ) (hw : ∀ x y, 0 ≤ w x y)
    (f : V → ℝ) (hf : mass w f = 0) (m : ℝ) :
    normSq w f ≤ normSq w (fun x => f x - m) := by
  have hpoint (x : V) : row w x * (f x - m)^2 =
      row w x * f x ^ 2 - (2 * m) * (row w x * f x) + m^2 * row w x := by ring
  have heq : normSq w (fun x => f x - m) =
      normSq w f - 2 * m * mass w f + m^2 * (∑ x, row w x) := by
    unfold normSq mass
    simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [heq, hf, mul_zero, sub_zero]
  have hW : 0 ≤ ∑ x, row w x := Finset.sum_nonneg fun x _ => row_nonneg hw x
  have hm := mul_nonneg (sq_nonneg m) hW
  linarith

/-- Full generic mean-zero Rayleigh bound, with the median genuinely constructed. -/
theorem mean_zero_rayleigh [Nonempty V] (w : V → V → ℝ)
    (hw : ∀ x y, 0 ≤ w x y) (hsym : ∀ x y, w x y = w y x)
    (h : ℝ) (hh : 0 ≤ h) (f : V → ℝ) (hf : mass w f = 0)
    (hcut : ∀ S : Finset V, 0 < volume w S →
      volume w S ≤ (∑ x, row w x) / 2 → h * volume w S ≤ cut w S) :
    (h ^ 2 / 2) * normSq w f ≤ energy w f := by
  classical
  obtain ⟨m, hmlo, hmhi⟩ := exists_weighted_median (row w) (row_nonneg hw) f
  have hpos : volume w (support (positivePart f m)) ≤ (∑ x, row w x) / 2 := by
    simpa [volume, positivePart, lt_max_iff, sub_pos] using hmhi
  have hneg : volume w (support (negativePart f m)) ≤ (∑ x, row w x) / 2 := by
    simpa [volume, negativePart, lt_max_iff, sub_pos] using hmlo
  have hp := one_sided_rayleigh w hw hsym h hh (positivePart f m)
    (fun x => le_max_right _ _) hpos hcut
  have hn := one_sided_rayleigh w hw hsym h hh (negativePart f m)
    (fun x => le_max_right _ _) hneg hcut
  have hnorm : normSq w f ≤ normSq w (positivePart f m) + normSq w (negativePart f m) := by
    rw [normSq_parts]
    exact normSq_shift_mean_zero w hw f hf m
  calc
    (h ^ 2 / 2) * normSq w f ≤
        (h ^ 2 / 2) * (normSq w (positivePart f m) + normSq w (negativePart f m)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (h ^ 2 / 2) * normSq w (positivePart f m) +
        (h ^ 2 / 2) * normSq w (negativePart f m) := by ring
    _ ≤ energy w (positivePart f m) + energy w (negativePart f m) := add_le_add hp hn
    _ ≤ energy w f := energy_parts_le w hw f m

end Erdos642.CampaignFe72210bContinuation3.WeightedMedian
