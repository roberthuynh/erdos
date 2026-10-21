import Erdos1017.WeightedLayers
import Erdos1017.RootedTypeLift

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Local triangle packing for product capacities. Every vertex has its own leave bound. -/
structure LocalTrianglePacking (x : ι → ℝ) where
  mass : Finset ι → ℝ
  nonneg : ∀ T, 0 ≤ mass T
  supported : ∀ T, T.card ≠ 3 → mass T=0
  pair_cap : ∀ B, B.card=2 → subsetMoment mass B ≤ ∏ i ∈ B,x i
  leave : ∀ i, x i*((∑ j,x j)-x i)-2*subsetMoment mass {i} ≤ (x i)^2

noncomputable def starTriangleMass (x : ι → ℝ) : Finset (Option ι) → ℝ :=
  aggregateMass rootedPartSet (weightedLayer x 2)

theorem rootedPartSet_card (T : Finset ι) : (rootedPartSet T).card=T.card+1 := by
  have hn : none ∉ T.image some := by simp
  simp [rootedPartSet,Finset.card_insert_of_notMem hn,Finset.card_image_of_injective _ (Option.some_injective ι)]

theorem starTriangleMass_supported (x : ι → ℝ) (S : Finset (Option ι)) (hS : S.card ≠ 3) :
    starTriangleMass x S=0 := by
  apply Finset.sum_eq_zero
  intro T _
  dsimp [weightedLayer]
  split_ifs with hT hcard
  · have h := congrArg Finset.card hT
    rw [rootedPartSet_card,hcard] at h
    exact (hS h.symm).elim
  all_goals rfl

theorem starTriangleMass_moment (x : ι → ℝ) (B : Finset (Option ι)) :
    subsetMoment (starTriangleMass x) B =
      ∑ T : Finset ι, if B ⊆ rootedPartSet T then weightedLayer x 2 T else 0 := by
  have h := aggregate_observable rootedPartSet (weightedLayer x 2)
    (fun S => if B ⊆ S then (1:ℝ) else 0)
  simpa only [subsetMoment,starTriangleMass,mul_ite,mul_one,mul_zero] using h

theorem starTriangleMass_root (x : ι → ℝ) :
    subsetMoment (starTriangleMass x) {none} = elementarySum Finset.univ x 2 := by
  rw [starTriangleMass_moment]
  simp only [Finset.singleton_subset_iff,none_mem_rootedPartSet,if_true]
  exact weightedLayer_total x 2

theorem starTriangleMass_singleton (x : ι → ℝ) (i : ι) :
    subsetMoment (starTriangleMass x) {some i} = x i*((∑ j,x j)-x i) := by
  rw [starTriangleMass_moment]
  simp only [Finset.singleton_subset_iff,some_mem_rootedPartSet]
  have hm := weightedLayer_singleton_moment x i 1
  simp only [subsetMoment,Finset.singleton_subset_iff] at hm
  rw [hm,weighted_elementarySum_one]
  have h := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
  congr 1
  linarith

theorem starTriangleMass_root_pair (x : ι → ℝ) (i : ι) :
    subsetMoment (starTriangleMass x) {none,some i} = x i*((∑ j,x j)-x i) := by
  have h : subsetMoment (starTriangleMass x) {none,some i} =
      subsetMoment (starTriangleMass x) {some i} := by
    rw [starTriangleMass_moment,starTriangleMass_moment]
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,none_mem_rootedPartSet,some_mem_rootedPartSet,true_and]
  rw [h,starTriangleMass_singleton]

theorem starTriangleMass_minor_pair (x : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    subsetMoment (starTriangleMass x) {some i,some j} = x i*x j := by
  rw [starTriangleMass_moment]
  simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,some_mem_rootedPartSet]
  have h := weightedLayer_top_moment x {i,j}
  simpa [subsetMoment,Finset.insert_subset_iff,Finset.singleton_subset_iff,hij] using h

/-- A root equal to the sum of the other weights has an explicit local packing. -/
noncomputable def balancedTrianglePacking (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    LocalTrianglePacking (fun o : Option ι => o.elim (∑ i,x i) x) where
  mass := starTriangleMass x
  nonneg := aggregateMass_nonneg rootedPartSet (weightedLayer x 2) (fun T => by
    dsimp [weightedLayer]; split_ifs
    · exact Finset.prod_nonneg (fun i _ => hx i)
    · exact le_rfl)
  supported := starTriangleMass_supported x
  pair_cap B hB := by
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hB
    rw [Finset.prod_pair hij]
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        rw [starTriangleMass_root_pair]
        simp only [Option.elim_none,Option.elim_some]
        nlinarith [sq_nonneg (x j)]
    | some i =>
      cases j with
      | none =>
        rw [Finset.pair_comm,starTriangleMass_root_pair]
        simp only [Option.elim_none,Option.elim_some]
        nlinarith [sq_nonneg (x i)]
      | some j =>
        rw [starTriangleMass_minor_pair x i j (fun h => hij (congrArg some h))]
        rfl
  leave i := by
    rw [Fintype.sum_option]
    simp only [Option.elim_none,Option.elim_some]
    cases i with
    | none =>
      rw [starTriangleMass_root]
      simp only [Option.elim_none]
      have he := elementarySum_nonneg Finset.univ x (fun i _ => hx i) 2
      nlinarith
    | some i =>
      rw [starTriangleMass_singleton]
      simp only [Option.elim_some]
      nlinarith [sq_nonneg (x i)]

end Erdos1017
