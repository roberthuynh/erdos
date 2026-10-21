import Erdos1017.TrianglePackingStep
import Mathlib.Logic.Equiv.Option

namespace Erdos1017
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem renamed_subsetMoment (e : κ ≃ ι) (t : Finset ι → ℝ) (B : Finset κ) :
    subsetMoment (fun S => t (e.finsetCongr S)) B = subsetMoment t (e.finsetCongr B) := by
  unfold subsetMoment
  rw [← e.finsetCongr.sum_comp]
  simp only [Equiv.finsetCongr_apply,Finset.map_subset_map]

noncomputable def LocalTrianglePacking.rename (x : ι → ℝ) (e : κ ≃ ι)
    (P : LocalTrianglePacking x) : LocalTrianglePacking (fun i => x (e i)) where
  mass S := P.mass (e.finsetCongr S)
  nonneg S := P.nonneg _
  supported S hS := P.supported _ (by simpa only [Equiv.finsetCongr_apply,Finset.card_map] using hS)
  pair_cap B hB := by
    rw [renamed_subsetMoment]
    have h := P.pair_cap (e.finsetCongr B) (by simpa only [Equiv.finsetCongr_apply,Finset.card_map] using hB)
    simpa [Equiv.finsetCongr_apply,Finset.prod_map] using h
  leave i := by
    rw [renamed_subsetMoment]
    have hs : (∑ j : κ,x (e j))=∑ j : ι,x j := e.sum_comp x
    simpa only [hs,Equiv.finsetCongr_apply,Finset.map_singleton,Equiv.toEmbedding_apply] using P.leave (e i)

noncomputable def zeroRootMass (t : Finset ι → ℝ) : Finset (Option ι) → ℝ :=
  aggregateMass (fun T : Finset ι => T.image some) t

theorem zeroRootMass_moment (t : Finset ι → ℝ) (B : Finset (Option ι)) :
    subsetMoment (zeroRootMass t) B =
      ∑ T : Finset ι, if B ⊆ T.image some then t T else 0 := by
  have h := aggregate_observable (fun T : Finset ι => T.image some) t
    (fun S => if B ⊆ S then (1:ℝ) else 0)
  simpa only [subsetMoment,zeroRootMass,mul_ite,mul_one,mul_zero] using h

theorem zeroRootMass_root_moment (t : Finset ι → ℝ) (B : Finset (Option ι)) (hB : none ∈ B) :
    subsetMoment (zeroRootMass t) B=0 := by
  rw [zeroRootMass_moment]
  apply Finset.sum_eq_zero
  intro T _
  have h : ¬ B ⊆ T.image some := by
    intro h
    have hn := h hB
    simpa using hn
  simp [h]

theorem zeroRootMass_minor_moment (t : Finset ι → ℝ) (B : Finset ι) :
    subsetMoment (zeroRootMass t) (B.image some)=subsetMoment t B := by
  rw [zeroRootMass_moment]
  simp only [Finset.image_subset_image_iff (Option.some_injective ι)]
  rfl

noncomputable def LocalTrianglePacking.addZeroRoot (x : ι → ℝ) (P : LocalTrianglePacking x) :
    LocalTrianglePacking (fun o : Option ι => o.elim 0 x) where
  mass := zeroRootMass P.mass
  nonneg := aggregateMass_nonneg _ P.mass P.nonneg
  supported S hS := by
    apply Finset.sum_eq_zero
    intro T _
    dsimp
    split_ifs with hT
    · apply P.supported T
      have hc : T.card=S.card := by
        rw [← hT,Finset.card_image_of_injective _ (Option.some_injective ι)]
      omega
    · rfl
  pair_cap B hB := by
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hB
    rw [Finset.prod_pair hij]
    cases i with
    | none =>
      rw [zeroRootMass_root_moment _ _ (by simp)]
      simp
    | some i =>
      cases j with
      | none =>
        rw [zeroRootMass_root_moment _ _ (by simp)]
        simp
      | some j =>
        have h := zeroRootMass_minor_moment P.mass {i,j}
        simp only [Finset.image_insert,Finset.image_singleton] at h
        rw [h]
        have hij' : i ≠ j := fun h => hij (congrArg some h)
        simpa [hij'] using P.pair_cap {i,j} (by simp [hij'])
  leave i := by
    rw [Fintype.sum_option]
    simp only [Option.elim_none,Option.elim_some,zero_add]
    cases i with
    | none =>
      rw [zeroRootMass_root_moment _ _ (by simp)]
      simp
    | some i =>
      have h := zeroRootMass_minor_moment P.mass {i}
      simp only [Finset.image_singleton] at h
      rw [h]
      exact P.leave i

end Erdos1017
