import Erdos1017.TypeCentral
import Erdos1017.TypeInflationBound

namespace Erdos1017
open scoped BigOperators
universe u

/-- The sharp affine budget for arbitrary finite positive part weights.
Induction removes one part; the enlarged root is supplied by an explicit construction. -/
theorem multipartite_weight_partition {ι : Type u} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i,0 < x i) :
    ∃ P : TypePartition x,P.cost x ≤ typeBudget x := by
  have main : ∀ n : ℕ, ∀ (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α=n → ∀ y : α → ℝ, (∀ i,0 < y i) →
      ∃ P : TypePartition y,P.cost y ≤ typeBudget y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro α _ _ hn y hy
      cases isEmpty_or_nonempty α with
      | inl hempty =>
        letI := hempty
        let P : TypePartition y := {
          mass := fun _ => 0
          nonneg := fun _ => le_rfl
          pair_exact := fun i _ _ => isEmptyElim i }
        refine ⟨P,?_⟩
        simp [TypePartition.cost,P,typeBudget]
      | inr hnonempty =>
        letI := hnonempty
        obtain ⟨g,_,hmax⟩ := Finset.exists_max_image Finset.univ y Finset.univ_nonempty
        let β := {i : α // i ≠ g}
        let z : β → ℝ := fun i => y i
        let a := y g
        let b := ∑ i,z i
        let e := Equiv.optionSubtypeNe g
        have ha : 0 < a := hy g
        have hz : ∀ i,0 ≤ z i := fun i => (hy i).le
        have hzmax : ∀ i,z i ≤ a := fun i => hmax i (Finset.mem_univ _)
        have hcard : Fintype.card β < n := by
          have he : Fintype.card (Option β)=Fintype.card α := Fintype.card_congr e
          rw [Fintype.card_option] at he
          omega
        have R : ∃ P : TypePartition (fun o : Option β => o.elim a z),
            P.cost _ ≤ typeBudget (fun o : Option β => o.elim a z) := by
          by_cases hlo : 9*a ≤ 2*(a+b)
          · exact low_type_partition a ha z hz hzmax hlo
          by_cases hhi : b ≤ 2*a
          · exact high_root_type_partition a ha z hz hzmax hhi
          by_cases hmid : 17*a ≤ 8*b
          · have hsratio : (∑ i,z i/a)=b/a := by simp only [div_eq_mul_inv,Finset.sum_mul,b]
            apply central_type_partition a ha z hz hzmax
            · rw [hsratio]
              apply (le_div_iff₀ ha).mpr
              linarith
            · rw [hsratio]
              apply (div_le_iff₀ ha).mpr
              linarith
          · obtain ⟨P,hP⟩ := ih (Fintype.card β) hcard β rfl z (fun i => hy i)
            exact inflation_type_partition a ha z hz hzmax (by linarith) (by linarith) P hP
        have hw : (fun o : Option β => o.elim a z)=fun o => y (e o) := by
          funext o
          cases o <;> rfl
        rw [hw] at R
        obtain ⟨P,hP⟩ := R
        have hP' : P.cost _ ≤ typeBudget y := hP.trans_eq (typeBudget_rename y e)
        let Q := P.rename _ e.symm
        have hQ : Q.cost _ ≤ typeBudget y := (TypePartition.rename_cost _ e.symm P).trans_le hP'
        have hout : ∃ Q : TypePartition (fun i => y (e (e.symm i))),Q.cost _ ≤ typeBudget y := ⟨Q,hQ⟩
        have heq : (fun i => y (e (e.symm i)))=y := by
          funext i
          rw [Equiv.apply_symm_apply]
        rw [heq] at hout
        exact hout
  exact main (Fintype.card ι) ι rfl x hx

end Erdos1017
