import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Finite weighted coarea by peeling the least positive value, and its genuine
cut-to-one-sided-Rayleigh consequence. No spectral inequality is a premise. -/
namespace Erdos642.CampaignFe72210bContinuation3.FiniteCoarea

open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def support (f : V → ℝ) : Finset V :=
  Finset.univ.filter fun x => 0 < f x
noncomputable def row (w : V → V → ℝ) (x : V) : ℝ := ∑ y, w x y
noncomputable def mass (w : V → V → ℝ) (f : V → ℝ) : ℝ := ∑ x, row w x * f x
noncomputable def volume (w : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ x, if x ∈ S then row w x else 0
noncomputable def indicator (S : Finset V) (x : V) : ℝ := if x ∈ S then 1 else 0
noncomputable def variation (w : V → V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ x, ∑ y, w x y * |f x - f y|
noncomputable def cut (w : V → V → ℝ) (S : Finset V) : ℝ :=
  (1 / 2 : ℝ) * variation w (indicator S)
noncomputable def energy (w : V → V → ℝ) (f : V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, ∑ y, w x y * (f x - f y)^2
noncomputable def normSq (w : V → V → ℝ) (f : V → ℝ) : ℝ := mass w (fun x => f x ^ 2)
noncomputable def peel (f : V → ℝ) (m : ℝ) (x : V) : ℝ :=
  if f x = 0 then 0 else f x - m

omit [DecidableEq V] in
@[simp] theorem mem_support (f : V → ℝ) (x : V) : x ∈ support f ↔ 0 < f x := by
  simp [support]

omit [DecidableEq V] in
theorem row_nonneg {w : V → V → ℝ} (hw : ∀ x y, 0 ≤ w x y) (x : V) :
    0 ≤ row w x := Finset.sum_nonneg fun y _ => hw x y

omit [DecidableEq V] in
theorem mass_nonneg {w : V → V → ℝ} (hw : ∀ x y, 0 ≤ w x y)
    {f : V → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ mass w f := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (row_nonneg hw x) (hf x)

omit [DecidableEq V] in
theorem variation_nonneg {w : V → V → ℝ} (hw : ∀ x y, 0 ≤ w x y) (f : V → ℝ) :
    0 ≤ variation w f := by
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (hw x y) (abs_nonneg _)

theorem cut_nonneg {w : V → V → ℝ} (hw : ∀ x y, 0 ≤ w x y) (S : Finset V) :
    0 ≤ cut w S := mul_nonneg (by norm_num) (variation_nonneg hw _)

theorem volume_mono {w : V → V → ℝ} (hw : ∀ x y, 0 ≤ w x y)
    {S T : Finset V} (hST : S ⊆ T) : volume w S ≤ volume w T := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ S
  · simp [hx, hST hx]
  · simp only [hx, if_false]
    split_ifs <;> simp [row_nonneg hw]

/-- The symmetric cut definition is exactly the directed crossing-weight sum. -/
theorem cut_eq_crossing (w : V → V → ℝ) (hsym : ∀ x y, w x y = w y x)
    (S : Finset V) :
    cut w S = ∑ x, ∑ y, if x ∈ S ∧ y ∉ S then w x y else 0 := by
  have hpoint (x y : V) : w x y * |indicator S x - indicator S y| =
      (if x ∈ S ∧ y ∉ S then w x y else 0) +
      (if y ∈ S ∧ x ∉ S then w x y else 0) := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
      simp [indicator, hx, hy]
  have hswap : (∑ x, ∑ y, if y ∈ S ∧ x ∉ S then w x y else 0) =
      ∑ x, ∑ y, if x ∈ S ∧ y ∉ S then w x y else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hsym y x]
  simp only [cut, variation, hpoint, Finset.sum_add_distrib]
  rw [hswap]
  ring

private theorem peel_abs (a b m : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (_hm : 0 ≤ m) (hmina : a = 0 ∨ m ≤ a) (hminb : b = 0 ∨ m ≤ b) :
    |a - b| = |(if a = 0 then 0 else a - m) - (if b = 0 then 0 else b - m)| +
      m * |(if 0 < a then (1 : ℝ) else 0) - (if 0 < b then (1 : ℝ) else 0)| := by
  by_cases ha0 : a = 0
  · subst a
    by_cases hb0 : b = 0
    · simp [hb0]
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hmb : m ≤ b := hminb.resolve_left hb0
      simp [hb0, hbp, abs_of_nonneg hb, abs_of_nonpos (sub_nonpos.mpr hmb)]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hma : m ≤ a := hmina.resolve_left ha0
    by_cases hb0 : b = 0
    · subst b
      simp [ha0, hap, abs_of_nonneg ha, abs_of_nonneg (sub_nonneg.mpr hma)]
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      simp [ha0, hb0, hap, hbp, sub_sub_sub_cancel_right]

/-- Exact finite coarea inequality, proved by finite least-level peeling. -/
theorem coarea (w : V → V → ℝ) (_hw : ∀ x y, 0 ≤ w x y)
    (h : ℝ) (_hh : 0 ≤ h) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hcut : ∀ S : Finset V, S ⊆ support f → h * volume w S ≤ cut w S) :
    2 * h * mass w f ≤ variation w f := by
  suffices H : ∀ n : ℕ, ∀ f : V → ℝ, (support f).card ≤ n →
      (∀ x, 0 ≤ f x) →
      (∀ S : Finset V, S ⊆ support f → h * volume w S ≤ cut w S) →
      2 * h * mass w f ≤ variation w f from
    H (support f).card f le_rfl hf hcut
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hn hf hcut
    by_cases hS : (support f).Nonempty
    · obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image (support f) f hS
      let m := f z
      have hm : 0 < m := (mem_support f z).mp hz
      let r := peel f m
      have hlow (x : V) : f x = 0 ∨ m ≤ f x := by
        by_cases hx : f x = 0
        · exact Or.inl hx
        · exact Or.inr (hmin x ((mem_support f x).mpr (lt_of_le_of_ne (hf x) (Ne.symm hx))))
      have hr (x : V) : 0 ≤ r x := by
        dsimp [r, peel]
        split_ifs with hx
        · rfl
        · exact sub_nonneg.mpr ((hlow x).resolve_left hx)
      have hsub : support r ⊆ support f := by
        intro x hx
        have hxpos := (mem_support r x).mp hx
        by_contra hxnot
        have hx0 : f x = 0 := le_antisymm (le_of_not_gt (by simpa using hxnot)) (hf x)
        simp [r, peel, hx0] at hxpos
      have hznot : z ∉ support r := by simp [r, peel, m]
      have hcard : (support r).card < (support f).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
          intro heq
          exact hznot (heq.symm ▸ hz)⟩)
      have hind := ih (support r).card (lt_of_lt_of_le hcard hn) r le_rfl hr
        (fun S hSr => hcut S (hSr.trans hsub))
      have hmass : mass w f = mass w r + m * volume w (support f) := by
        have hpoint (x : V) : f x = r x + m * indicator (support f) x := by
          by_cases hx : f x = 0
          · simp [r, peel, indicator, hx]
          · have hxp : 0 < f x := lt_of_le_of_ne (hf x) (Ne.symm hx)
            simp [r, peel, indicator, hx, hxp]
        simp only [mass, volume]
        conv_lhs => arg 2; ext x; rw [hpoint x]
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ support f <;> simp [indicator, hx]
        ring
      have hvar : variation w f = variation w r + 2 * m * cut w (support f) := by
        have hpoint (x y : V) : |f x - f y| = |r x - r y| +
            m * |indicator (support f) x - indicator (support f) y| := by
          simpa [r, peel, indicator] using peel_abs (f x) (f y) m (hf x) (hf y)
            hm.le (hlow x) (hlow y)
        simp only [variation, cut, hpoint, mul_add, Finset.sum_add_distrib]
        simp_rw [mul_left_comm (w _ _) m, ← Finset.mul_sum]
        ring
      have htop := hcut (support f) (Finset.Subset.refl _)
      have hmcut := mul_le_mul_of_nonneg_left htop hm.le
      rw [hmass, hvar]
      nlinarith
    · have hf0 (x : V) : f x = 0 := by
        have hx : ¬ 0 < f x := by
          intro hx
          exact hS ⟨x, (mem_support f x).mpr hx⟩
        exact le_antisymm (le_of_not_gt hx) (hf x)
      simp [mass, variation, hf0]

omit [DecidableEq V] in
/-- Weighted finite Cauchy--Schwarz and incidence counting, with no cut premise. -/
theorem variation_sq_le_energy_norm (w : V → V → ℝ)
    (hw : ∀ x y, 0 ≤ w x y) (hsym : ∀ x y, w x y = w y x) (f : V → ℝ) :
    (variation w (fun x => f x ^ 2)) ^ 2 ≤ 8 * energy w f * normSq w f := by
  let a : V × V → ℝ := fun p => w p.1 p.2 * |f p.1 ^ 2 - f p.2 ^ 2|
  let b : V × V → ℝ := fun p => w p.1 p.2 * (f p.1 - f p.2)^2
  let c : V × V → ℝ := fun p => w p.1 p.2 * (f p.1 + f p.2)^2
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (V × V))
    (r := a) (f := b) (g := c)
    (fun p _ => mul_nonneg (hw _ _) (sq_nonneg _))
    (fun p _ => mul_nonneg (hw _ _) (sq_nonneg _))
    (fun p _ => by dsimp [a, b, c]; rw [mul_pow, sq_abs]; nlinarith [sq_nonneg (w p.1 p.2)])
  have hbound : (∑ p : V × V, c p) ≤ 4 * normSq w f := by
    have hterm (x y : V) : w x y * (f x + f y)^2 ≤
        2 * w x y * (f x ^ 2 + f y ^ 2) := by
      have := mul_nonneg (hw x y) (sq_nonneg (f x - f y))
      nlinarith
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (V × V)))
      (fun p _ => hterm p.1 p.2)
    have hswap : (∑ x, ∑ y, w x y * f y ^ 2) = ∑ x, row w x * f x ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp_rw [hsym _ x]
      simp [row, Finset.sum_mul]
    calc
      (∑ p : V × V, c p) ≤ ∑ p : V × V,
          2 * w p.1 p.2 * (f p.1 ^ 2 + f p.2 ^ 2) := hsum
      _ = 4 * normSq w f := by
        simp only [Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib]
        simp_rw [mul_assoc, ← Finset.mul_sum]
        rw [hswap]
        have hfirst : (∑ x, ∑ y, w x y * f x ^ 2) = normSq w f := by
          simp [normSq, mass, row, Finset.sum_mul]
        rw [hfirst]
        change 2 * normSq w f + 2 * normSq w f = 4 * normSq w f
        ring
  have hb : 0 ≤ ∑ p : V × V, b p :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hw _ _) (sq_nonneg _)
  have hfinal := hcs.trans (mul_le_mul_of_nonneg_left hbound hb)
  simp only [a, b, Fintype.sum_prod_type] at hfinal
  unfold variation energy
  nlinarith only [hfinal]

/-- A real cut lower bound implies the full one-sided Rayleigh inequality. -/
theorem one_sided_rayleigh (w : V → V → ℝ) (hw : ∀ x y, 0 ≤ w x y)
    (hsym : ∀ x y, w x y = w y x) (h : ℝ) (hh : 0 ≤ h)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hsmall : volume w (support f) ≤ (∑ x, row w x) / 2)
    (hcut : ∀ S : Finset V, 0 < volume w S →
      volume w S ≤ (∑ x, row w x) / 2 → h * volume w S ≤ cut w S) :
    (h ^ 2 / 2) * normSq w f ≤ energy w f := by
  have hsupp : support (fun x => f x ^ 2) = support f := by
    ext x
    simp only [mem_support]
    constructor
    · intro hx
      nlinarith [hf x]
    · intro hx
      positivity
  have hc := coarea w hw h hh (fun x => f x ^ 2) (fun x => sq_nonneg _)
    (fun S hS => by
      have hvol0 : 0 ≤ volume w S := by
        unfold volume
        exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [row_nonneg hw]
      rcases hvol0.eq_or_lt with hz | hp
      · rw [← hz, mul_zero]
        exact cut_nonneg hw S
      · exact hcut S hp ((volume_mono hw (hsupp ▸ hS)).trans hsmall))
  have hn : 0 ≤ normSq w f := mass_nonneg hw (fun x => sq_nonneg _)
  have he : 0 ≤ energy w f := by
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ =>
      Finset.sum_nonneg fun y _ => mul_nonneg (hw x y) (sq_nonneg _))
  have hv := variation_nonneg hw (fun x => f x ^ 2)
  have hcs := variation_sq_le_energy_norm w hw hsym f
  change 2 * h * normSq w f ≤ _ at hc
  rcases hn.eq_or_lt with hz | hp
  · rw [← hz, mul_zero]
    exact he
  · have hsq : (2 * h * normSq w f)^2 ≤
        (variation w (fun x => f x ^ 2))^2 :=
      (sq_le_sq₀ (mul_nonneg (mul_nonneg (by norm_num) hh) hn) hv).mpr hc
    have hmul : (h ^ 2 * normSq w f - 2 * energy w f) * normSq w f ≤ 0 := by
      nlinarith only [hsq, hcs]
    have hcancel : h ^ 2 * normSq w f - 2 * energy w f ≤ 0 := by
      by_contra hbad
      have hpositive := mul_pos (lt_of_not_ge hbad) hp
      linarith only [hmul, hpositive]
    nlinarith only [hcancel]

end Erdos642.CampaignFe72210bContinuation3.FiniteCoarea
