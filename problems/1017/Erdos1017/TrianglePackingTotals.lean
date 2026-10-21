import Erdos1017.LocalTriangleLeave

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem triangle_pair_moments_total (t : Finset ι → ℝ)
    (ht : ∀ T,T.card ≠ 3 → t T=0) :
    (∑ B ∈ (Finset.univ : Finset ι).powersetCard 2,subsetMoment t B)=3*∑ T,t T := by
  unfold subsetMoment
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [← Finset.sum_filter]
  have he : ((Finset.univ : Finset ι).powersetCard 2).filter (fun B => B ⊆ T)=T.powersetCard 2 := by
    ext B
    simp [Finset.mem_powersetCard,and_comm]
  rw [he]
  by_cases hT : T.card=3
  · simp [Finset.card_powersetCard,hT]
  · simp [ht T hT]

theorem LocalTrianglePacking.total_bound (x : ι → ℝ) (P : LocalTrianglePacking x) :
    6*(∑ T,P.mass T) ≤ (∑ i,x i)^2-∑ i,(x i)^2 := by
  have hcap : (∑ B ∈ (Finset.univ : Finset ι).powersetCard 2,subsetMoment P.mass B) ≤
      elementarySum Finset.univ x 2 := by
    apply Finset.sum_le_sum
    intro B hB
    exact P.pair_cap B (Finset.mem_powersetCard.mp hB).2
  rw [triangle_pair_moments_total P.mass P.supported] at hcap
  have he := elementarySum_two_identity Finset.univ x
  linarith

/-- A balanced minor vector supplies all three partial-triangle budgets. -/
theorem partial_triangle_supply_balanced (x : ι → ℝ) (hx : ∀ i,0 ≤ x i)
    (a : ℝ) (hb : 0 < ∑ i,x i) (ha : (∑ i,x i)/2 ≤ a) (hab : a ≤ ∑ i,x i)
    (hbalanced : ∀ i,2*x i ≤ ∑ j,x j) :
    ∃ t : Finset ι → ℝ, (∀ T,T.card ≠ 3 → t T=0) ∧ (∀ T,0 ≤ t T) ∧
      (∀ B,B.card=2 → subsetMoment t B ≤ ∏ i ∈ B,x i) ∧
      (∀ i,x i*((∑ j,x j)-a-x i) ≤ subsetMoment t {i}) ∧
      (∑ T,t T) ≤ ((∑ i,x i)-a)*((∑ i,x i)^2-∑ i,(x i)^2)/(3*(∑ i,x i)) := by
  obtain ⟨P⟩ := local_triangle_leave_exists x hx hbalanced
  let b := ∑ i,x i
  let d := b-a
  let θ := 2*d/b
  have hd : 0 ≤ d := sub_nonneg.mpr hab
  have hθ : 0 ≤ θ := div_nonneg (by positivity) hb.le
  have hθ1 : θ ≤ 1 := by
    apply (div_le_one hb).mpr
    dsimp [d,b]
    linarith
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hθb : θ*b=2*d := by dsimp [θ]; field_simp [hb0]
  refine ⟨fun T => θ*P.mass T, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT; dsimp only; rw [P.supported T hT,mul_zero]
  · intro T; exact mul_nonneg hθ (P.nonneg T)
  · intro B hB
    rw [subsetMoment_mul]
    exact (mul_le_mul_of_nonneg_left (P.pair_cap B hB) hθ).trans
      (mul_le_of_le_one_left (Finset.prod_nonneg (fun i _ => hx i)) hθ1)
  · intro i
    rw [subsetMoment_mul]
    have hl := mul_le_mul_of_nonneg_left (P.leave i) hθ
    have hsmall := mul_le_mul_of_nonneg_right hθ1 (sq_nonneg (x i))
    have hid := congrArg (fun z : ℝ => z*x i) hθb
    change x i*(d-x i) ≤ _
    dsimp [b] at hid
    nlinarith
  · rw [← Finset.mul_sum]
    have ht := mul_le_mul_of_nonneg_left (P.total_bound x) hθ
    apply (le_div_iff₀ (show 0 < 3*b by positivity)).mpr
    have hid := congrArg (fun z : ℝ => z*((∑ i,x i)^2-∑ i,(x i)^2)) hθb
    have ht' := mul_le_mul_of_nonneg_left ht hb.le
    change (θ*(∑ T,P.mass T))*(3*b) ≤ d*((∑ i,x i)^2-∑ i,(x i)^2)
    nlinarith

end Erdos1017
