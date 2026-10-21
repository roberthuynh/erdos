import Erdos1017.PartialTriangleHeavy

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The partial-triangle hypotheses hold for every eligible minor weight vector. -/
theorem partial_triangle_supply_exists (x : ι → ℝ) (hx : ∀ i,0 ≤ x i)
    (a : ℝ) (hb : 0 < ∑ i,x i) (ha : (∑ i,x i)/2 ≤ a) (hab : a ≤ ∑ i,x i)
    (hmax : ∀ i,x i ≤ a) : Nonempty (PartialTriangleSupply a x) := by
  by_cases heq : a=∑ i,x i
  · subst a
    exact ⟨emptyPartialTriangleSupply x hx⟩
  have halt : a < ∑ i,x i := lt_of_le_of_ne hab heq
  by_cases hbalanced : ∀ i,2*x i ≤ ∑ j,x j
  · obtain ⟨t,ht,h0,hpair,hquota,htotal⟩ := partial_triangle_supply_balanced x hx a hb ha hab hbalanced
    exact ⟨⟨t,ht,h0,hpair,hquota,htotal⟩⟩
  · push_neg at hbalanced
    obtain ⟨g,hg⟩ := hbalanced
    let β := {i : ι // i ≠ g}
    let y : β → ℝ := fun i => x i
    let e := Equiv.optionSubtypeNe g
    have hy : ∀ i,0 ≤ y i := fun i => hx i
    have hsum : x g+(∑ i,y i)=∑ i,x i := packing_split_sum x g
    have hs : 0 < ∑ i,y i := by linarith [hmax g]
    have hheavy : (∑ i,y i) ≤ x g := by linarith
    have hab' : a ≤ x g+∑ i,y i := by linarith
    let P := heavyPartialTriangleSupply y hy (x g) a hs hheavy (hmax g) hab'
    have hw : (fun o : Option β => o.elim (x g) y)=fun o => x (e o) := by
      funext o
      cases o <;> rfl
    have P' : PartialTriangleSupply a (fun o => x (e o)) := hw ▸ P
    have Q := PartialTriangleSupply.rename a _ e.symm P'
    exact ⟨by simpa using Q⟩

end Erdos1017
