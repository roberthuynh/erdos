import Erdos1017.WeightedLayers

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def quadraticRootMass (a : ℝ) (x : ι → ℝ) (T : Finset ι) : ℝ :=
  weightedLayer (fun i => x i*(a-(∑ j,x j)+x i)) 1 T + weightedLayer x 2 T

theorem quadraticRootMass_singleton_moment (a : ℝ) (x : ι → ℝ) (i : ι) :
    subsetMoment (quadraticRootMass a x) {i} = a*x i := by
  unfold quadraticRootMass
  rw [subsetMoment_add]
  have h1 := weightedLayer_top_moment (fun i => x i*(a-(∑ j,x j)+x i)) {i}
  simp only [Finset.card_singleton, Finset.prod_singleton] at h1
  rw [h1, weightedLayer_singleton_moment x i 1, weighted_elementarySum_one]
  have hs := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
  nlinarith [congrArg (fun z : ℝ => x i*z) hs]

theorem quadraticRootMass_pair_moment (a : ℝ) (x : ι → ℝ) (B : Finset ι) (hB : B.card = 2) :
    subsetMoment (quadraticRootMass a x) B = ∏ i ∈ B,x i := by
  unfold quadraticRootMass
  rw [subsetMoment_add, weightedLayer_moment_zero _ B 1 (by omega)]
  simpa only [hB, zero_add] using weightedLayer_top_moment x B

theorem quadraticRootMass_total (a : ℝ) (x : ι → ℝ) :
    (∑ T, quadraticRootMass a x T) = a*(∑ i,x i)-elementarySum Finset.univ x 2 := by
  unfold quadraticRootMass
  rw [Finset.sum_add_distrib, weightedLayer_total, weightedLayer_total, weighted_elementarySum_one]
  have hs : (∑ i,x i*(a-(∑ j,x j)+x i)) =
      (a-(∑ j,x j))*(∑ i,x i)+∑ i,(x i)^2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  have h := elementarySum_two_identity Finset.univ x
  nlinarith

noncomputable def triangleCorrection (t : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ T : Finset ι, t T*tripleTrade T S

theorem triangleCorrection_moment (t : Finset ι → ℝ)
    (ht : ∀ T, T.card ≠ 3 → t T=0) (B : Finset ι) (hB : B.card ≤ 2) :
    subsetMoment (triangleCorrection t) B=0 := by
  unfold triangleCorrection
  rw [subsetMoment_finset_sum]
  apply Finset.sum_eq_zero
  intro T _
  rw [subsetMoment_mul]
  by_cases hT : T.card=3
  · rw [tripleTrade_zero_moment T B hT hB, mul_zero]
  · rw [ht T hT, zero_mul]

theorem triangleCorrection_empty (t : Finset ι → ℝ)
    (ht : ∀ T, T.card ≠ 3 → t T=0) : triangleCorrection t ∅ = ∑ T,t T := by
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : T.card=3
  · simp [tripleTrade, layerMass, Finset.mem_powersetCard]
  · simp [ht T hT]

theorem triangleCorrection_singleton (t : Finset ι → ℝ)
    (ht : ∀ T, T.card ≠ 3 → t T=0) (S : Finset ι) (hS : S.card=1) :
    triangleCorrection t S = -subsetMoment t S := by
  unfold triangleCorrection subsetMoment
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : T.card=3
  · have hn : S ≠ ∅ := by intro h; simp [h] at hS
    by_cases hST : S ⊆ T <;> simp [tripleTrade,layerMass,Finset.mem_powersetCard,hS,hn,hST]
  · simp [ht T hT]

theorem triangleCorrection_pair (t : Finset ι → ℝ)
    (ht : ∀ T, T.card ≠ 3 → t T=0) (S : Finset ι) (hS : S.card=2) :
    triangleCorrection t S = subsetMoment t S := by
  unfold triangleCorrection subsetMoment
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : T.card=3
  · have hn : S ≠ ∅ := by intro h; simp [h] at hS
    by_cases hST : S ⊆ T <;> simp [tripleTrade,layerMass,Finset.mem_powersetCard,hS,hn,hST]
  · simp [ht T hT]

theorem triangleCorrection_large (t : Finset ι → ℝ)
    (ht : ∀ T, T.card ≠ 3 → t T=0) (S : Finset ι) (hS : 3 ≤ S.card) :
    triangleCorrection t S = -t S := by
  have he (T : Finset ι) : t T*tripleTrade T S = -(if T=S then t S else 0) := by
    by_cases hT : T.card=3
    · have hn : S ≠ ∅ := by intro h; simp [h] at hS
      have h1 : S.card ≠ 1 := by omega
      have h2 : S.card ≠ 2 := by omega
      have htop := layerMass_top T S
      rw [hT] at htop
      simp only [tripleTrade]
      rw [show layerMass T 0 S=0 by simp [layerMass,hn],
        show layerMass T 1 S=0 by simp [layerMass,Finset.mem_powersetCard,h1],
        show layerMass T 2 S=0 by simp [layerMass,Finset.mem_powersetCard,h2],htop]
      by_cases h : T=S
      · subst T; simp
      · simp [h,Ne.symm h]
    · by_cases h : T=S
      · subst T; simp [ht S hT]
      · simp [ht T hT,h]
  unfold triangleCorrection
  simp_rw [he]
  simp

noncomputable def partialTriangleMass (a : ℝ) (x : ι → ℝ) (t : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  if S.Nonempty then quadraticRootMass a x S-triangleCorrection t S else 0

theorem partialTriangleMass_moment (a : ℝ) (x : ι → ℝ) (t : Finset ι → ℝ)
    (ht : ∀ T, T.card ≠ 3 → t T=0) (B : Finset ι) (hB0 : B.Nonempty) (hB : B.card ≤ 2) :
    subsetMoment (partialTriangleMass a x t) B = subsetMoment (quadraticRootMass a x) B := by
  have he : subsetMoment (partialTriangleMass a x t) B =
      subsetMoment (fun S => quadraticRootMass a x S-triangleCorrection t S) B := by
    apply Finset.sum_congr rfl
    intro S _
    by_cases hBS : B ⊆ S
    · simp [partialTriangleMass,hBS,hB0.mono hBS]
    · simp [partialTriangleMass,hBS]
  rw [he,subsetMoment_sub,triangleCorrection_moment t ht B hB,sub_zero]

theorem partialTriangleMass_nonneg (a : ℝ) (x : ι → ℝ) (t : Finset ι → ℝ)
    (ht : ∀ T, T.card ≠ 3 → t T=0) (ht0 : ∀ T, 0 ≤ t T)
    (hpair : ∀ B, B.card=2 → subsetMoment t B ≤ ∏ i ∈ B,x i)
    (hquota : ∀ i, x i*((∑ j,x j)-a-x i) ≤ subsetMoment t {i}) :
    ∀ S, 0 ≤ partialTriangleMass a x t S := by
  intro S
  unfold partialTriangleMass
  split_ifs with hS
  · by_cases h1 : S.card=1
    · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h1
      rw [triangleCorrection_singleton t ht {i} (by simp)]
      simp only [quadraticRootMass,weightedLayer,Finset.card_singleton,Finset.prod_singleton]
      simp only [if_true,show (1:ℕ) ≠ 2 by omega,if_false,add_zero,sub_neg_eq_add]
      have h := hquota i
      nlinarith
    by_cases h2 : S.card=2
    · rw [triangleCorrection_pair t ht S h2]
      simp only [quadraticRootMass,weightedLayer,h2,show (2:ℕ) ≠ 1 by omega,if_false,if_true,zero_add]
      exact sub_nonneg.mpr (hpair S h2)
    · have h3 : 3 ≤ S.card := by have := hS.card_pos; omega
      rw [triangleCorrection_large t ht S h3]
      simp only [quadraticRootMass,weightedLayer,h1,h2,if_false,zero_add,zero_sub,neg_neg]
      exact ht0 S
  · exact le_rfl

theorem partialTriangleMass_total (a : ℝ) (x : ι → ℝ) (t : Finset ι → ℝ)
    (ht : ∀ T, T.card ≠ 3 → t T=0) :
    (∑ S, partialTriangleMass a x t S) =
      a*(∑ i,x i)-elementarySum Finset.univ x 2+∑ T,t T := by
  have he (S : Finset ι) : partialTriangleMass a x t S =
      quadraticRootMass a x S-triangleCorrection t S + (if S=∅ then ∑ T,t T else 0) := by
    by_cases hS : S=∅
    · subst S
      simp [partialTriangleMass,quadraticRootMass,weightedLayer,triangleCorrection_empty t ht]
    · simp [partialTriangleMass,Finset.nonempty_iff_ne_empty.mpr hS,hS]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,quadraticRootMass_total]
  have hz := triangleCorrection_moment t ht ∅ (by simp)
  simp only [subsetMoment,Finset.empty_subset,if_true] at hz
  rw [hz]
  simp

end Erdos1017
