import Erdos1017.BinomialReduction

namespace Erdos1017.Binomial
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def selected (b : V → Bool) : Finset V :=
  Finset.univ.filter (fun i => b i=true)

theorem inclusion_eq (B : Finset V) (b : V → Bool) :
    inclusionIndicator B b = if B ⊆ selected b then 1 else 0 := by
  by_cases h : B ⊆ selected b
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    have hb : b i=true := by simpa [selected] using h hi
    simp [hb]
  · rw [if_neg h]
    obtain ⟨i,hi,hni⟩ := Finset.not_subset.mp h
    apply Finset.prod_eq_zero hi
    have hb : b i=false := by simpa [selected] using hni
    simp [hb]

theorem selector_subset_moment (p : V → ℝ) (B : Finset V) :
    (∑ b : V → Bool, if B ⊆ selected b then selectorMass p b else 0)=∏ i ∈ B,p i := by
  have h := selector_inclusion p B
  simp_rw [inclusion_eq,mul_ite,mul_one,mul_zero] at h
  exact h

theorem count_subsets_erase (S : Finset V) (r : V) (k : ℕ) :
    ((S.erase r).card.choose k : ℝ)=
      ∑ B ∈ (Finset.univ.erase r).powersetCard k,if B ⊆ S then (1:ℝ) else 0 := by
  have he : ((Finset.univ.erase r).powersetCard k).filter (fun B => B ⊆ S)=
      (S.erase r).powersetCard k := by
    ext B
    simp only [Finset.mem_filter,Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hu,hk⟩,hS⟩
      refine ⟨?_,hk⟩
      intro i hi
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hu hi)).1,hS hi⟩
    · rintro ⟨hS,hk⟩
      refine ⟨⟨?_,hk⟩,?_⟩
      · intro i hi
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hS hi)).1,Finset.mem_univ i⟩
      · intro i hi
        exact (Finset.mem_erase.mp (hS hi)).2
  rw [Finset.sum_boole,he,Finset.card_powersetCard]

/-- The selector has every higher inclusion moment, not only pair marginals. -/
theorem scaled_selector_moment (w : V → ℕ) (a : ℝ) (ha : a ≠ 0)
    (t : ℕ) (B : Finset V) :
    (∑ b : V → Bool,if B ⊆ selected b
      then a^t*selectorMass (fun i => w i/a) b else 0)=
      a^t*((∏ i ∈ B,(w i : ℝ))/a^B.card) := by
  have he (b : V → Bool) :
      (if B ⊆ selected b then a^t*selectorMass (fun i => w i/a) b else 0)=
      a^t*(if B ⊆ selected b then selectorMass (fun i => w i/a) b else 0) := by
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.mul_sum,selector_subset_moment,Finset.prod_div_distrib]
  simp

end Erdos1017.Binomial
