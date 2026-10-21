import Erdos1017.TrianglePackingTotals

namespace Erdos1017
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

structure PartialTriangleSupply (a : ℝ) (x : ι → ℝ) where
  mass : Finset ι → ℝ
  supported : ∀ T,T.card ≠ 3 → mass T=0
  nonneg : ∀ T,0 ≤ mass T
  pair_cap : ∀ B,B.card=2 → subsetMoment mass B ≤ ∏ i ∈ B,x i
  quota : ∀ i,x i*((∑ j,x j)-a-x i) ≤ subsetMoment mass {i}
  total : (∑ T,mass T) ≤ ((∑ i,x i)-a)*((∑ i,x i)^2-∑ i,(x i)^2)/(3*(∑ i,x i))

noncomputable def PartialTriangleSupply.rename (a : ℝ) (x : ι → ℝ) (e : κ ≃ ι)
    (P : PartialTriangleSupply a x) : PartialTriangleSupply a (fun i => x (e i)) where
  mass S := P.mass (e.finsetCongr S)
  supported S hS := P.supported _ (by simpa only [Equiv.finsetCongr_apply,Finset.card_map] using hS)
  nonneg S := P.nonneg _
  pair_cap B hB := by
    rw [renamed_subsetMoment]
    have h := P.pair_cap (e.finsetCongr B) (by simpa only [Equiv.finsetCongr_apply,Finset.card_map] using hB)
    simpa [Equiv.finsetCongr_apply,Finset.prod_map] using h
  quota i := by
    rw [renamed_subsetMoment,e.sum_comp x]
    simpa only [Equiv.finsetCongr_apply,Finset.map_singleton,Equiv.toEmbedding_apply] using P.quota (e i)
  total := by
    rw [e.finsetCongr.sum_comp P.mass,e.sum_comp x,e.sum_comp (fun i => (x i)^2)]
    exact P.total

noncomputable def emptyPartialTriangleSupply (x : ι → ℝ) (hx : ∀ i,0 ≤ x i) : PartialTriangleSupply (∑ i,x i) x where
  mass _ := 0
  supported _ _ := rfl
  nonneg _ := le_rfl
  pair_cap B _ := by
    simp only [subsetMoment,ite_self,Finset.sum_const_zero]
    exact Finset.prod_nonneg (fun i _ => hx i)
  quota i := by simp only [subsetMoment,ite_self,Finset.sum_const_zero,sub_self,zero_sub,mul_neg]; nlinarith [sq_nonneg (x i)]
  total := by simp

end Erdos1017
