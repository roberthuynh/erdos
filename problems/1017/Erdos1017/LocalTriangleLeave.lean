import Erdos1017.TrianglePackingHeavy

namespace Erdos1017
open scoped BigOperators
universe u

/-- A nonnegative product-capacity instance with no weight above half its total
has a triangle packing with leave at most the square of each individual weight. -/
theorem local_triangle_leave_exists {ι : Type u} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i,0 ≤ x i) (hbal : ∀ i,2*x i ≤ ∑ j,x j) :
    Nonempty (LocalTrianglePacking x) := by
  have main : ∀ n : ℕ, ∀ (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α=n → ∀ y : α → ℝ, (∀ i,0 ≤ y i) →
      (∀ i,2*y i ≤ ∑ j,y j) → Nonempty (LocalTrianglePacking y) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro α _ _ hn y hy hbalanced
      cases isEmpty_or_nonempty α with
      | inl hempty =>
        letI := hempty
        refine ⟨{
          mass := fun _ => 0
          nonneg := fun _ => le_rfl
          supported := fun _ _ => rfl
          pair_cap := ?_
          leave := ?_}⟩
        · intro B hB
          have hz : B=∅ := Subsingleton.elim _ _
          simp [hz] at hB
        · intro i
          exact isEmptyElim i
      | inr hnonempty =>
        letI := hnonempty
        obtain ⟨g,_,hmax⟩ := Finset.exists_max_image Finset.univ y Finset.univ_nonempty
        let β := {i : α // i ≠ g}
        let z : β → ℝ := fun i => y i
        let e := Equiv.optionSubtypeNe g
        have hz : ∀ i,0 ≤ z i := fun i => hy i
        have hzmax : ∀ i,z i ≤ y g := fun i => hmax i (Finset.mem_univ _)
        have hsum : y g+(∑ i,z i)=∑ i,y i := packing_split_sum y g
        have hg : y g ≤ ∑ i,z i := by linarith [hbalanced g]
        by_cases heq : y g=∑ i,z i
        · exact packing_balanced_at y hy g (by linarith)
        · have hlt : y g < ∑ i,z i := lt_of_le_of_ne hg heq
          have hcard : Fintype.card β < n := by
            have he : Fintype.card (Option β)=Fintype.card α := Fintype.card_congr e
            rw [Fintype.card_option] at he
            omega
          have P : Nonempty (LocalTrianglePacking (fun o : Option β => o.elim (y g) z)) := by
            by_cases htail : ∀ i,2*z i ≤ ∑ j,z j
            · obtain ⟨Q⟩ := ih (Fintype.card β) hcard β rfl z hz htail
              exact packing_extend_balanced_tail z hz (y g) (hy g) hzmax hlt Q
            · push_neg at htail
              obtain ⟨i,hi⟩ := htail
              exact packing_extend_heavy_tail z hz (y g) hzmax hlt i (by linarith)
          obtain ⟨P⟩ := P
          have hw : (fun o : Option β => o.elim (y g) z) = fun o => y (e o) := by
            funext o
            cases o <;> rfl
          have P' : LocalTrianglePacking (fun o => y (e o)) := hw ▸ P
          have Q := LocalTrianglePacking.rename _ e.symm P'
          exact ⟨by simpa using Q⟩
  exact main (Fintype.card ι) ι rfl x hx hbal

end Erdos1017
