import Openmath.IncidenceRepair.AdditiveCorrection
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Finite counting reduction of Pexider correction to additive correction.
The four tested equations are those in §2.2 of the published #85 proof.
This file proves only the reduction, not the projective-incidence theorem. -/

namespace Erdos85.IncidenceRepair.Pexider

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H]

noncomputable def error (f g c : G → H) (u b : G) : ℝ :=
  if g (u + b) = f u + c b then 0 else 1

noncomputable def defect (f : G → H) (a x y : G) : ℝ :=
  if f (a + (x + y)) - f a = (f (a + x) - f a) + (f (a + y) - f a)
  then 0 else 1

noncomputable def errorCount (f g c : G → H) : ℝ := ∑ u, ∑ b, error f g c u b

noncomputable def defectCount (f : G → H) (a : G) : ℝ := ∑ x, ∑ y, defect f a x y

lemma error_nonneg (f g c : G → H) (u b : G) : 0 ≤ error f g c u b := by
  classical
  unfold error
  split_ifs <;> norm_num

lemma four_equations (f g c : G → H) (a b x y : G)
    (h₁ : g ((a + x) + (b + y)) = f (a + x) + c (b + y))
    (h₂ : g ((a + x + y) + b) = f (a + x + y) + c b)
    (h₃ : g (a + (b + y)) = f a + c (b + y))
    (h₄ : g ((a + y) + b) = f (a + y) + c b) :
    f (a + (x + y)) - f a = (f (a + x) - f a) + (f (a + y) - f a) := by
  have e₁ : f (a + x) + c (b + y) = f (a + x + y) + c b := by
    rw [← h₁, ← h₂]
    congr 1
    abel
  have e₂ : f a + c (b + y) = f (a + y) + c b := by
    rw [← h₃, ← h₄]
    congr 1
    abel
  have hs := congrArg₂ (fun u v : H => u - v) e₁ e₂
  simp only [add_sub_add_right_eq_sub] at hs
  calc
    f (a + (x + y)) - f a = (f (a + x + y) - f (a + y)) +
        (f (a + y) - f a) := by rw [← add_assoc]; abel
    _ = (f (a + x) - f a) + (f (a + y) - f a) := by rw [← hs]

lemma defect_le_four_errors (f g c : G → H) (a b x y : G) :
    defect f a x y ≤ error f g c (a + x) (b + y) +
      error f g c (a + x + y) b + error f g c a (b + y) +
      error f g c (a + y) b := by
  classical
  have h := four_equations f g c a b x y
  unfold defect error
  split_ifs <;> simp_all <;> norm_num

lemma sum_add_left (k : G) (F : G → ℝ) : (∑ x, F (k + x)) = ∑ x, F x := by
  exact Equiv.sum_comp (Equiv.addLeft k) F

lemma sum_add_right (k : G) (F : G → ℝ) : (∑ x, F (x + k)) = ∑ x, F x := by
  simpa only [add_comm] using sum_add_left k F

lemma sum_error_shift (f g c : G → H) (x y : G) :
    (∑ a, ∑ b, error f g c (a + x) (b + y)) = errorCount f g c := by
  simp_rw [sum_add_right]
  exact sum_add_right x (fun a => ∑ b, error f g c a b)

lemma sum_error_shift_first (f g c : G → H) (x : G) :
    (∑ a, ∑ b, error f g c (a + x) b) = errorCount f g c := by
  exact sum_add_right x (fun a => ∑ b, error f g c a b)

lemma sum_error_shift_second (f g c : G → H) (y : G) :
    (∑ a, ∑ b, error f g c a (b + y)) = errorCount f g c := by
  simp_rw [sum_add_right]
  rfl

lemma total_defect_bound (f g c : G → H) :
    (Fintype.card G : ℝ) * (∑ a, defectCount f a) ≤
      4 * (Fintype.card G : ℝ) ^ 2 * errorCount f g c := by
  classical
  have h : (∑ x, ∑ y, ∑ a, ∑ b : G, defect f a x y) ≤
      ∑ x, ∑ y, ∑ a, ∑ b,
        (error f g c (a + x) (b + y) + error f g c (a + x + y) b +
          error f g c a (b + y) + error f g c (a + y) b) := by
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      defect_le_four_errors f g c a b x y
  have hr : (∑ x, ∑ y, ∑ a, ∑ b,
        (error f g c (a + x) (b + y) + error f g c (a + x + y) b +
          error f g c a (b + y) + error f g c (a + y) b)) =
      4 * (Fintype.card G : ℝ) ^ 2 * errorCount f g c := by
    simp_rw [Finset.sum_add_distrib, add_assoc]
    simp_rw [sum_error_shift, sum_error_shift_first, sum_error_shift_second]
    simp
    ring
  have hl : (∑ x, ∑ y, ∑ a, ∑ b : G, defect f a x y) =
      (Fintype.card G : ℝ) * (∑ a, defectCount f a) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp_rw [← Finset.mul_sum]
    congr 1
    unfold defectCount
    calc
      (∑ x, ∑ y, ∑ a, defect f a x y) = ∑ x, ∑ a, ∑ y, defect f a x y := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
      _ = ∑ a, ∑ x, ∑ y, defect f a x y := Finset.sum_comm
  rw [hr, hl] at h
  exact h

/-- A translate has at most four times the original number of Pexider failures. -/
theorem exists_translate_small_defect (f g c : G → H) :
    ∃ a : G, defectCount f a ≤ 4 * errorCount f g c := by
  classical
  have hq : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have h := total_defect_bound f g c
  have havg : (∑ a, defectCount f a) ≤ (Fintype.card G : ℝ) *
      (4 * errorCount f g c) := by
    nlinarith [h]
  by_contra hn
  push Not at hn
  have hs := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty : (Finset.univ : Finset G).Nonempty)
    (fun a (_ : a ∈ (Finset.univ : Finset G)) => hn a)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  linarith

/-- Normalized version used with the Pexider error fraction in the plane lemma. -/
theorem exists_translate_defect_fraction (f g c : G → H) (r : ℝ)
    (h : errorCount f g c ≤ r * (Fintype.card G : ℝ) ^ 2) :
    ∃ a : G, defectCount f a ≤ (4 * r) * (Fintype.card G : ℝ) ^ 2 := by
  obtain ⟨a, ha⟩ := exists_translate_small_defect f g c
  exact ⟨a, by nlinarith⟩

/-- The first Pexider correction: `f` is close to an additive map plus a constant. -/
theorem correct_first_function (f g c : G → H) (r : ℝ)
    (hr : 0 ≤ r) (hsmall : 4 * r < 1 / 6)
    (herr : errorCount f g c ≤ r * (Fintype.card G : ℝ) ^ 2) :
    ∃ (h : G →+ H) (α : H),
      count (fun x => f x ≠ h x + α) ≤ 8 * r * Fintype.card G := by
  classical
  obtain ⟨a, ha⟩ := exists_translate_defect_fraction f g c r herr
  let A : G → H := fun x => f (a + x) - f a
  have heq : additiveDefect A = defectCount f a := by
    unfold additiveDefect
    rw [count_prod (fun x y => A (x+y) ≠ A x+A y)]
    unfold count defectCount
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    dsimp only [A]
    unfold defect
    split_ifs <;> simp_all
  obtain ⟨h, hh⟩ := additive_correction A (4 * r) (by positivity) hsmall (by rwa [heq])
  let α := f a - h a
  refine ⟨h, α, ?_⟩
  have hpred (x : G) : (A x ≠ h x) ↔ f (a+x) ≠ h (a+x)+α := by
    have he : h (a+x)+α = h x+f a := by simp only [map_add, α]; abel
    rw [he]
    simp only [A, ne_eq, sub_eq_iff_eq_add]
  have hc : count (fun x => A x ≠ h x) = count (fun x => f x ≠ h x+α) := by
    calc
      _ = count (fun x => f (a+x) ≠ h (a+x)+α) := by exact congrArg count (funext fun x => propext (hpred x))
      _ = _ := count_equiv (Equiv.addLeft a) (fun x => f x ≠ h x+α)
  rw [hc] at hh
  nlinarith


lemma errorCount_eq_count (f g c : G → H) :
    errorCount f g c = count (fun z : G × G => g (z.1+z.2) ≠ f z.1+c z.2) := by
  classical
  unfold errorCount
  rw [count_prod (fun u b => g (u+b) ≠ f u+c b)]
  apply Finset.sum_congr rfl
  intro u _
  unfold count
  apply Finset.sum_congr rfl
  intro b _
  unfold error
  split_ifs <;> simp_all

lemma count_pair_first (p : G → Prop) :
    count (fun z : G × G => p z.1) = count p * Fintype.card G := by
  classical
  rw [count_prod (fun u (_ : G) => p u)]
  unfold count
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  ring

lemma count_shear (L R : G → H) :
    count (fun z : G × G => L (z.1+z.2) ≠ R z.2) =
    count (fun z : G × G => L z.1 ≠ R z.2) := by
  let e : G × G ≃ G × G :=
    { toFun := fun z => (z.1+z.2,z.2)
      invFun := fun z => (z.1-z.2,z.2)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp }
  exact count_equiv e (fun z => L z.1 ≠ R z.2)

lemma corrected_pair_error (f g c : G → H) (h : G →+ H) (α : H) :
    count (fun z : G × G => g z.1-h z.1 ≠ α+c z.2-h z.2) ≤
      errorCount f g c + count (fun u => f u ≠ h u+α) * Fintype.card G := by
  classical
  let L := fun z => g z-h z
  let R := fun b => α+c b-h b
  have hm : count (fun z : G × G => L (z.1+z.2) ≠ R z.2) ≤
      count (fun z : G × G => (g (z.1+z.2) ≠ f z.1+c z.2) ∨
        (f z.1 ≠ h z.1+α)) := by
    apply count_mono
    intro z hz
    by_contra hn
    push Not at hn
    apply hz
    simp only [L, R, hn.1, hn.2, map_add]
    abel
  rw [count_shear] at hm
  have hu := count_or_le
    (fun z : G × G => g (z.1+z.2) ≠ f z.1+c z.2)
    (fun z : G × G => f z.1 ≠ h z.1+α)
  rw [← errorCount_eq_count, count_pair_first (fun u => f u ≠ h u+α)] at hu
  exact hm.trans hu

/-- Full additive Pexider correction, with the constants used in §2.2. -/
theorem pexider_correction (f g c : G → H) (r : ℝ)
    (hr : 0 ≤ r) (hsmall : 4*r < 1/6)
    (herr : errorCount f g c ≤ r * (Fintype.card G : ℝ)^2) :
    ∃ (h : G →+ H) (α β : H),
      count (fun x => f x ≠ h x+α) ≤ 8*r*Fintype.card G ∧
      count (fun x => g x ≠ h x+α+β) ≤ 18*r*Fintype.card G ∧
      count (fun x => c x ≠ h x+β) ≤ 9*r*Fintype.card G := by
  classical
  obtain ⟨h, α, hf⟩ := correct_first_function f g c r hr hsmall herr
  have he := corrected_pair_error f g c h α
  have hq : (0 : ℝ) ≤ Fintype.card G := by positivity
  have he' : count (fun z : G × G => g z.1-h z.1 ≠ α+c z.2-h z.2) ≤
      (9*r) * (Fintype.card G : ℝ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hf hq]
  obtain ⟨β₀, hc, hg⟩ := independent_lists_concentrate
    (fun z => g z-h z) (fun b => α+c b-h b) (9*r) (by positivity) (by linarith) he'
  let β := β₀-α
  refine ⟨h, α, β, hf, ?_, ?_⟩
  · have hp (x : G) : (g x-h x ≠ β₀) ↔ g x ≠ h x+α+β := by
      have heq : h x+α+β = β₀+h x := by dsimp [β]; abel
      rw [heq]
      simp only [ne_eq, sub_eq_iff_eq_add]
    have hh : count (fun x => g x-h x ≠ β₀) = count (fun x => g x ≠ h x+α+β) := by
      exact congrArg count (funext fun x => propext (hp x))
    rw [hh] at hg
    nlinarith
  · have hp (x : G) : (α+c x-h x ≠ β₀) ↔ c x ≠ h x+β := by
      have heq : α+c x-h x = β₀ ↔ c x = h x+β := by
        dsimp [β]
        constructor
        · intro heq
          calc
            c x = (α+c x-h x)+h x-α := by abel
            _ = h x+(β₀-α) := by rw [heq]; abel
        · intro heq
          rw [heq]
          abel
      exact not_congr heq
    have hh : count (fun x => α+c x-h x ≠ β₀) = count (fun x => c x ≠ h x+β) := by
      exact congrArg count (funext fun x => propext (hp x))
    rwa [hh] at hc

/-- A protected row fixes the additive correction at its specified input. -/
theorem fixed_row_recovers (f g c : G → H) (h : G →+ H) (α β : H) (i : G)
    (hsum : count (fun b => g (i+b) ≠ f i+c b) +
      count (fun z => g z ≠ h z+α+β) + count (fun b => c b ≠ h b+β) <
        Fintype.card G) : f i = h i+α := by
  classical
  let p := fun b => g (i+b) ≠ f i+c b
  let r := fun b => g (i+b) ≠ h (i+b)+α+β
  let s := fun b => c b ≠ h b+β
  have hr : count r = count (fun z => g z ≠ h z+α+β) :=
    count_equiv (Equiv.addLeft i) (fun z => g z ≠ h z+α+β)
  have hu : count (fun b => p b ∨ r b ∨ s b) < Fintype.card G := by
    have h₁ := count_or_le p (fun b => r b ∨ s b)
    have h₂ := count_or_le r s
    change count p + _ + count s < _ at hsum
    rw [← hr] at hsum
    linarith
  obtain ⟨b, hb⟩ := exists_of_count_lt_card _ hu
  simp only [not_or, not_not, p, r, s] at hb
  apply add_right_cancel (b := h b+β)
  calc
    f i+(h b+β) = g (i+b) := by rw [← hb.2.2, hb.1]
    _ = (h i+α)+(h b+β) := by rw [hb.2.1, map_add]; abel

/-- Agreement of the two corrected functions fixes their relative translation. -/
theorem diagonal_recovers (f g : G → H) (h : G →+ H) (α β : H)
    (hsum : count (fun x => g x ≠ f x) + count (fun x => f x ≠ h x+α) +
      count (fun x => g x ≠ h x+α+β) < Fintype.card G) : β = 0 := by
  classical
  let p := fun x => g x ≠ f x
  let r := fun x => f x ≠ h x+α
  let s := fun x => g x ≠ h x+α+β
  have hu : count (fun x => p x ∨ r x ∨ s x) < Fintype.card G := by
    have h₁ := count_or_le p (fun x => r x ∨ s x)
    have h₂ := count_or_le r s
    change count p + count r + count s < _ at hsum
    linarith
  obtain ⟨x, hx⟩ := exists_of_count_lt_card _ hu
  simp only [not_or, not_not, p, r, s] at hx
  apply add_left_cancel (a := h x+α)
  rw [← hx.2.2, hx.1, hx.2.1, add_zero]

/-- Protected values remove both translations, including the value at one. -/
theorem protected_pexider [One G] [One H] (f g c : G → H) (η : ℝ)
    (hη : 0 ≤ η) (hsmall : η ≤ 1/10000000)
    (herr : errorCount f g c ≤ (36*η) * (Fintype.card G : ℝ)^2)
    (hrow : ∀ i : G, i = 0 ∨ i = 1 →
      count (fun b => g (i+b) ≠ f i+c b) ≤ 20*η*Fintype.card G)
    (hdiag : count (fun x => g x ≠ f x) ≤ 36*η*Fintype.card G)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) :
    ∃ h : G →+ H, h 1 = 1 ∧
      count (fun x => f x ≠ h x) ≤ 288*η*Fintype.card G ∧
      count (fun x => g x ≠ h x) ≤ 648*η*Fintype.card G := by
  classical
  obtain ⟨h, α, β, hf, hg, hc⟩ :=
    pexider_correction f g c (36*η) (by positivity) (by linarith) herr
  have hq : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hbound : η*(Fintype.card G : ℝ) ≤ (1/10000000)*(Fintype.card G : ℝ) :=
    mul_le_mul_of_nonneg_right hsmall (le_of_lt hq)
  have hfix (i : G) (hi : i = 0 ∨ i = 1) : f i = h i+α := by
    apply fixed_row_recovers f g c h α β i
    have hri := hrow i hi
    nlinarith
  have ha : α = 0 := by simpa [hf0] using (hfix 0 (Or.inl rfl)).symm
  have hb : β = 0 := by
    apply diagonal_recovers f g h α β
    nlinarith
  refine ⟨h, ?_, ?_, ?_⟩
  · simpa [hf1, ha] using (hfix 1 (Or.inr rfl)).symm
  · simp only [ha, add_zero] at hf
    convert hf using 1 <;> ring
  · simp only [ha, hb, add_zero] at hg
    convert hg using 1 <;> ring

end Erdos85.IncidenceRepair.Pexider
