import Mathlib

/-! Finite counting for additive correction. Supporting results, not projective repair. -/
namespace Erdos85.IncidenceRepair
open scoped BigOperators
noncomputable section
variable {G H : Type*}

def count [Fintype G] (p : G → Prop) : ℝ := by
  classical
  exact ∑ x, if p x then 1 else 0

lemma count_nonneg [Fintype G] (p : G → Prop) : 0 ≤ count p := by
  classical
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

lemma count_le_card [Fintype G] (p : G → Prop) : count p ≤ Fintype.card G := by
  classical
  calc
    count p ≤ ∑ _ : G, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by
      split_ifs <;> norm_num
    _ = Fintype.card G := by simp

lemma count_mono [Fintype G] {p q : G → Prop} (h : ∀ x, p x → q x) :
    count p ≤ count q := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : p x <;> by_cases hq : q x <;> simp_all

lemma count_or_le [Fintype G] (p q : G → Prop) :
    count (fun x => p x ∨ q x) ≤ count p + count q := by
  classical
  unfold count
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]

lemma count_not [Fintype G] (p : G → Prop) :
    count (fun x => ¬ p x) = Fintype.card G - count p := by
  classical
  have h : count (fun x => ¬ p x) + count p = Fintype.card G := by
    unfold count
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : G, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hp : p x <;> simp [hp]
      _ = Fintype.card G := by simp
  linarith

lemma count_equiv [Fintype G] [Fintype H] (e : G ≃ H) (p : H → Prop) :
    count (fun x => p (e x)) = count p := by
  classical
  exact Equiv.sum_comp e (fun x => if p x then (1 : ℝ) else 0)

lemma count_prod [Fintype G] [Fintype H] (p : G → H → Prop) :
    count (fun z : G × H => p z.1 z.2) = ∑ x, count (p x) := by
  classical
  exact Fintype.sum_prod_type _

lemma count_eq_zero_iff [Fintype G] (p : G → Prop) : count p = 0 ↔ ∀ x, ¬ p x := by
  classical
  unfold count
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by split_ifs <;> norm_num)]
  simp

lemma exists_of_count_lt_card [Fintype G] (p : G → Prop)
    (h : count p < Fintype.card G) : ∃ x, ¬ p x := by
  classical
  by_contra hn
  have hp : ∀ x, p x := by simpa using hn
  have : count p = Fintype.card G := by simp [count, hp]
  linarith

lemma count_exists_le_average [Fintype G] [Nonempty G] (f : G → ℝ) :
    ∃ x, f x * Fintype.card G ≤ ∑ y, f y := by
  classical
  by_contra hn
  push Not at hn
  have h := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset G))
    Finset.univ_nonempty (fun x _ => hn x)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [← Finset.sum_mul] at h
  simp [mul_comm] at h

def additiveDefect [Fintype G] [Add G] [Add H] (A : G → H) : ℝ :=
  count fun z : G × G => A (z.1 + z.2) ≠ A z.1 + A z.2

def difference [Add G] [Sub H] (A : G → H) (x y : G) : H := A (x + y) - A y

lemma difference_cocycle [AddCommGroup G] [AddCommGroup H] (A : G → H) (x t y : G) :
    difference A (x+t) y = difference A x (t+y) + difference A t y := by
  simp only [difference]
  rw [add_assoc]
  abel

lemma difference_eq_of_two_equations [AddCommGroup G] [AddCommGroup H]
    (A : G → H) (x y z : G)
    (hy : A ((x+y)+z) = A (x+y) + A z)
    (hz : A (y+(x+z)) = A y + A (x+z)) :
    difference A x y = difference A x z := by
  have hh : (x+y)+z = y+(x+z) := by abel
  rw [hh, hz] at hy
  simp only [difference]
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa [add_comm] using hy.symm

lemma difference_collision_bound [Fintype G] [AddCommGroup G] [AddCommGroup H]
    (A : G → H) (x : G) :
    count (fun yz : G × G => difference A x yz.1 ≠ difference A x yz.2)
      ≤ 2 * additiveDefect A := by
  classical
  let p : G × G → Prop := fun yz => A ((x+yz.1)+yz.2) ≠ A (x+yz.1)+A yz.2
  let q : G × G → Prop := fun yz => A (yz.1+(x+yz.2)) ≠ A yz.1+A (x+yz.2)
  have hp : count p = additiveDefect A := by
    exact count_equiv (Equiv.prodCongr (Equiv.addLeft x) (Equiv.refl G))
      (fun yz : G × G => A (yz.1+yz.2) ≠ A yz.1+A yz.2)
  have hq : count q = additiveDefect A := by
    exact count_equiv (Equiv.prodCongr (Equiv.refl G) (Equiv.addLeft x))
      (fun yz : G × G => A (yz.1+yz.2) ≠ A yz.1+A yz.2)
  have hc : count (fun yz : G × G => difference A x yz.1 ≠ difference A x yz.2)
      ≤ count (fun yz => p yz ∨ q yz) := by
    apply count_mono
    intro yz h
    by_contra hn
    simp only [not_or, not_not, p, q] at hn
    exact h (difference_eq_of_two_equations A x yz.1 yz.2 hn.1 hn.2)
  calc
    _ ≤ count (fun yz => p yz ∨ q yz) := hc
    _ ≤ count p + count q := count_or_le p q
    _ = 2 * additiveDefect A := by rw [hp, hq]; ring

lemma exists_difference_mode [Fintype G] [AddCommGroup G] [AddCommGroup H]
    (A : G → H) (x : G) :
    ∃ h : H, count (fun y => difference A x y ≠ h) * Fintype.card G
      ≤ 2 * additiveDefect A := by
  classical
  obtain ⟨z, hz⟩ := count_exists_le_average
    (fun z : G => count (fun y => difference A x y ≠ difference A x z))
  refine ⟨difference A x z, hz.trans ?_⟩
  have hc := difference_collision_bound A x
  rw [count_prod (fun y z : G => difference A x y ≠ difference A x z)] at hc
  simpa only [ne_comm] using hc

/-- Global additive defect below one sixth yields an actual additive homomorphism. -/
theorem additive_correction [Fintype G] [AddCommGroup G] [AddCommGroup H]
    (A : G → H) (θ : ℝ) (_hθ : 0 ≤ θ) (hsmall : θ < 1/6)
    (hdef : additiveDefect A ≤ θ * (Fintype.card G : ℝ)^2) :
    ∃ h : G →+ H, count (fun x => A x ≠ h x) ≤ 2 * θ * Fintype.card G := by
  classical
  have hq : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  choose h hh using exists_difference_mode A
  have hmode (x : G) : count (fun y => difference A x y ≠ h x) ≤ 2*θ*Fintype.card G := by
    have h := hh x
    nlinarith
  have hadd (x t : G) : h (x+t) = h x + h t := by
    let p : G → Prop := fun y => difference A (x+t) y ≠ h (x+t)
    let r : G → Prop := fun y => difference A x (t+y) ≠ h x
    let s : G → Prop := fun y => difference A t y ≠ h t
    have hr : count r = count (fun y => difference A x y ≠ h x) :=
      count_equiv (Equiv.addLeft t) (fun y => difference A x y ≠ h x)
    have hu : count (fun y => p y ∨ r y ∨ s y) < Fintype.card G := by
      have h1 := count_or_le p (fun y => r y ∨ s y)
      have h2 := count_or_le r s
      have hp := hmode (x+t)
      have hs := hmode t
      have hx := hmode x
      change count p ≤ _ at hp
      change count s ≤ _ at hs
      rw [← hr] at hx
      nlinarith
    obtain ⟨y, hy⟩ := exists_of_count_lt_card _ hu
    simp only [not_or, not_not, p, r, s] at hy
    rw [← hy.1, ← hy.2.1, ← hy.2.2]
    exact difference_cocycle A x t y
  let hom : G →+ H := AddMonoidHom.mk' h hadd
  refine ⟨hom, ?_⟩
  have hrow (x : G) (hx : A x ≠ h x) :
      (Fintype.card G : ℝ)/2 ≤ count (fun y => A (x+y) ≠ A x + A y) := by
    have hc : count (fun y => ¬ (difference A x y ≠ h x)) ≤
        count (fun y => A (x+y) ≠ A x + A y) := by
      apply count_mono
      intro y hy heq
      have : difference A x y = A x := by simp [difference, heq]
      exact hx (this.symm.trans (not_ne_iff.mp hy))
    rw [count_not] at hc
    have hm := hmode x
    nlinarith
  have hsum : count (fun x => A x ≠ h x) * ((Fintype.card G : ℝ)/2)
      ≤ additiveDefect A := by
    unfold additiveDefect
    rw [count_prod (fun x y : G => A (x+y) ≠ A x+A y)]
    unfold count
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : A x ≠ h x
    · simpa [hx, count] using hrow x hx
    · simp only [hx, ↓reduceIte, zero_mul]
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  change count (fun x => A x ≠ h x) ≤ _
  nlinarith

/-- Near agreement of two independent lists forces both near a common value. -/
theorem independent_lists_concentrate [Fintype G] [Nonempty G]
    (f g : G → H) (ε : ℝ) (_he : 0 ≤ ε) (hesmall : ε ≤ 1/2)
    (herr : count (fun xy : G × G => f xy.1 ≠ g xy.2)
      ≤ ε * (Fintype.card G : ℝ)^2) :
    ∃ b, count (fun y => g y ≠ b) ≤ ε * Fintype.card G ∧
      count (fun x => f x ≠ b) ≤ 2*ε*Fintype.card G := by
  classical
  have hq : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  obtain ⟨z, hz⟩ := count_exists_le_average (fun x => count (fun y => f x ≠ g y))
  rw [count_prod (fun x y : G => f x ≠ g y)] at herr
  have hg : count (fun y => g y ≠ f z) ≤ ε*Fintype.card G := by
    have heq : count (fun y => f z ≠ g y) = count (fun y => g y ≠ f z) := by
      simp only [ne_comm]
    rw [heq] at hz
    nlinarith
  refine ⟨f z, hg, ?_⟩
  have hrows (x : G) (hx : f x ≠ f z) :
      (Fintype.card G : ℝ)/2 ≤ count (fun y => f x ≠ g y) := by
    have hm : count (fun y => ¬(g y ≠ f z)) ≤ count (fun y => f x ≠ g y) := by
      apply count_mono
      intro y hy heq
      exact hx (heq.trans (not_ne_iff.mp hy))
    rw [count_not] at hm
    nlinarith
  have hs : count (fun x => f x ≠ f z) * ((Fintype.card G : ℝ)/2)
      ≤ ∑ x, count (fun y => f x ≠ g y) := by
    unfold count
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : f x ≠ f z
    · simpa [hx, count] using hrows x hx
    · simp only [hx, ↓reduceIte, zero_mul]
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  nlinarith

end
end Erdos85.IncidenceRepair
