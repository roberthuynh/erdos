import Erdos1017.WeightedGraph

namespace Erdos1017
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def positiveSupport (x : V → ℝ) : Finset V :=
  Finset.univ.filter (fun i => 0 < x i)

/-- Transfer all weight at v to u without changing the fixed graph. -/
noncomputable def mergeWeight (x : V → ℝ) (u v : V) (i : V) : ℝ :=
  if i=u then x u+x v else if i=v then 0 else x i

theorem mergeWeight_nonneg (x : V → ℝ) (hx : ∀ i,0 ≤ x i) (u v i : V) :
    0 ≤ mergeWeight x u v i := by
  unfold mergeWeight
  split_ifs
  · exact add_nonneg (hx u) (hx v)
  · exact le_rfl
  · exact hx i

theorem mergeWeight_sum (x : V → ℝ) (u v : V) (huv : u ≠ v) :
    (∑ i,mergeWeight x u v i)=∑ i,x i := by
  have h (i : V) : mergeWeight x u v i=x i+(if i=u then x v else 0)-(if i=v then x v else 0) := by
    by_cases hiu : i=u
    · subst i; simp [mergeWeight,huv]
    · by_cases hiv : i=v
      · subst i; simp [mergeWeight,huv.symm]
      · simp [mergeWeight,hiu,hiv]
  simp only [h,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp

theorem mergeWeight_support (x : V → ℝ) (u v : V) (huv : u ≠ v)
    (hu : 0 < x u) (hv : 0 < x v) :
    positiveSupport (mergeWeight x u v)=(positiveSupport x).erase v := by
  ext i
  simp only [positiveSupport,Finset.mem_erase,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hiu : i=u
  · subst i; simp [positiveSupport,mergeWeight,huv,hu,add_pos hu hv]
  · by_cases hiv : i=v
    · subst i; simp [positiveSupport,mergeWeight,huv.symm]
    · simp [positiveSupport,mergeWeight,hiu,hiv]

theorem mergeWeight_card_lt (x : V → ℝ) (u v : V) (huv : u ≠ v)
    (hu : 0 < x u) (hv : 0 < x v) :
    (positiveSupport (mergeWeight x u v)).card < (positiveSupport x).card := by
  rw [mergeWeight_support x u v huv hu hv]
  exact Finset.card_erase_lt_of_mem (by simp [positiveSupport,hv])

theorem mergeWeight_pair_average (G : SimpleGraph V) (x : V → ℝ)
    (u v : V) (huv : u ≠ v) (hnon : ¬ G.Adj u v)
    (hu : 0 < x u) (hv : 0 < x v) (i j : V) (hij : G.Adj i j) :
    (x u/(x u+x v))*(mergeWeight x u v i*mergeWeight x u v j)+
      (x v/(x u+x v))*(mergeWeight x v u i*mergeWeight x v u j)=x i*x j := by
  have hden : x u+x v ≠ 0 := ne_of_gt (add_pos hu hv)
  have hnon' : ¬ G.Adj v u := fun h => hnon h.symm
  have hne : i ≠ j := hij.ne
  by_cases hiu : i=u <;> by_cases hiv : i=v <;>
    by_cases hju : j=u <;> by_cases hjv : j=v <;>
    simp_all [mergeWeight] <;> field_simp <;> ring

end Erdos1017
