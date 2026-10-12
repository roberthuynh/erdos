import GeneralStar.Boundary
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

def useSet (q : ℕ) (D : GraphData) (t z : ℕ) : Finset ℕ :=
  (range t).filter fun i => z ∈ prescribedLabels q D i

def useCount (q : ℕ) (D : GraphData) (t z : ℕ) : ℕ := (useSet q D t z).card

theorem useCount_succ (q : ℕ) (D : GraphData) (t z : ℕ) :
    useCount q D (t+1) z=useCount q D t z + if z ∈ prescribedLabels q D t then 1 else 0 := by
  unfold useCount useSet
  rw [range_add_one,filter_insert]
  by_cases hz : z ∈ prescribedLabels q D t
  · simp [hz,card_insert_of_notMem]
  · simp [hz]

theorem useCount_before_label (q : ℕ) (D : GraphData) (hq : 5 ≤ q)
    (hs : SeedHyp q D) (t z : ℕ) (hz : D.order+t ≤ z) : useCount q D t z=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hi,hzi⟩ := mem_filter.mp hi
  have hib := prescribedLabels_range q D hq hs i hzi
  have := mem_range.mp hi
  have := mem_range.mp hib
  omega

theorem list_count_indices (xs : List ℕ) (z : ℕ) :
    ((range xs.length).filter fun i => xs.getD i 0=z).card=xs.count z := by
  have he : ∀ xs : List ℕ,
      (∑ i ∈ range xs.length, if xs.getD i 0=z then 1 else 0)=xs.count z := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.length_cons,sum_range_succ']
      simp only [List.getD_cons_zero,List.getD_cons_succ]
      rw [ih]
      simp [List.count_cons]
  simpa using he xs

theorem startup_use_bound (q : ℕ) (D : GraphData) (_hq : 5 ≤ q)
    (hs : SeedHyp q D) (t z : ℕ) (hz : z < D.order) :
    useCount q D t z ≤ seedSlot q D z := by
  classical
  let F := useSet q D t z
  have hf : ∀ i ∈ F, ∃ j < q-1, (startupWord q D).getD (i+j*(q-1)) 0=z := by
    intro i hi
    obtain ⟨hit,hzi⟩ := mem_filter.mp hi
    by_cases hir : i < q-1
    · simp only [prescribedLabels,if_pos hir,startupLabels] at hzi
      obtain ⟨j,hj,hje⟩ := mem_image.mp hzi
      exact ⟨j,mem_range.mp hj,hje⟩
    · simp only [prescribedLabels,if_neg hir] at hzi
      obtain ⟨j,_,hje⟩ := mem_image.mp hzi
      omega
  let f : ℕ → ℕ := fun i => i+(if hi : i ∈ F then (hf i hi).choose else 0)*(q-1)
  have maps : Set.MapsTo f (F : Set ℕ)
      (((range (startupWord q D).length).filter fun k => (startupWord q D).getD k 0=z) : Set ℕ) := by
    intro i hi
    change i ∈ F at hi
    have hchoice := (hf i hi).choose_spec
    have hir : i < q-1 := by
      have hzi := (mem_filter.mp hi).2
      by_contra hni
      simp only [prescribedLabels,if_neg hni] at hzi
      obtain ⟨j,_,hje⟩ := mem_image.mp hzi
      omega
    apply mem_filter.mpr
    simp only [f,dif_pos hi]
    refine ⟨mem_range.mpr ?_,hchoice.2⟩
    rw [startupWord_length q D hs]
    nlinarith [hchoice.1]
  have inj : Set.InjOn f (F : Set ℕ) := by
    intro i hi j hj heq
    change i ∈ F at hi
    change j ∈ F at hj
    have hir : i < q-1 := by
      have hzi := (mem_filter.mp hi).2
      by_contra hni
      simp only [prescribedLabels,if_neg hni] at hzi
      obtain ⟨k,_,hke⟩ := mem_image.mp hzi
      omega
    have hjr : j < q-1 := by
      have hzi := (mem_filter.mp hj).2
      by_contra hnj
      simp only [prescribedLabels,if_neg hnj] at hzi
      obtain ⟨k,_,hke⟩ := mem_image.mp hzi
      omega
    simp only [f,dif_pos hi,dif_pos hj] at heq
    have hemod := congrArg (fun x => x%(q-1)) heq
    simpa [Nat.add_mod,Nat.mod_eq_of_lt hir,Nat.mod_eq_of_lt hjr] using hemod
  have hc := card_le_card_of_injOn f maps inj
  rw [list_count_indices] at hc
  exact hc.trans (allocateWord_count_le (seedSlot q D) _ (sort_nodup _ _) _ z)

theorem tail_use_bound (q : ℕ) (D : GraphData) (hq : 5 ≤ q)
    (hs : SeedHyp q D) (t z : ℕ) (hz : D.order ≤ z) : useCount q D t z ≤ q-1 := by
  have hr : 0 < q-1 := by omega
  let k := (z-D.order)/(q-1)
  have hsub : D.order+(z-D.order)=z := by omega
  have hrem := Nat.mod_add_div (z-D.order) (q-1)
  have hm := Nat.mod_lt (z-D.order) hr
  have incl : useSet q D t z ⊆ Ico ((k+1)*(q-1)) ((k+2)*(q-1)) := by
    intro i hi
    obtain ⟨_,hzi⟩ := mem_filter.mp hi
    by_cases hir : i < q-1
    · simp only [prescribedLabels,if_pos hir] at hzi
      obtain ⟨v,_,hve⟩ := mem_image.mp (startupLabels_subset q D hq hs i hir hzi)
      have hvb := D.labels.bounded v
      change D.label v < D.order at hvb
      omega
    · simp only [prescribedLabels,if_neg hir] at hzi
      obtain ⟨j,hj,hje⟩ := mem_image.mp hzi
      have hj' := mem_range.mp hj
      have hic := Nat.mod_add_div i (q-1)
      have him := Nat.mod_lt i hr
      have hid : 1 ≤ i/(q-1) := (Nat.le_div_iff_mul_le hr).mpr (by omega)
      have he : i/(q-1)-1=k := by
        have hdiv : (z-D.order)/(q-1)=i/(q-1)-1 := by
          have hzs : z-D.order=(i/(q-1)-1)*(q-1)+j := by omega
          rw [hzs,Nat.add_comm,Nat.add_mul_div_right _ _ hr,Nat.div_eq_of_lt hj',Nat.zero_add]
        exact hdiv.symm
      apply mem_Ico.mpr
      dsimp [k] at he ⊢
      have hes : i/(q-1)=((z-D.order)/(q-1))+1 := by omega
      rw [hes,Nat.mul_comm] at hic
      have hn : ((z-D.order)/(q-1)+2)*(q-1)=((z-D.order)/(q-1)+1)*(q-1)+(q-1) := by ring
      constructor
      · omega
      · rw [hn]; omega
  have hc := card_le_card incl
  rw [Nat.card_Ico] at hc
  unfold useCount
  have hk : (k+2)*(q-1)-((k+1)*(q-1))=q-1 := by
    have he : (k+2)*(q-1)=(k+1)*(q-1)+(q-1) := by ring
    rw [he,Nat.add_sub_cancel_left]
  exact hc.trans (by rw [hk])

end Erdos585.GeneralStar
