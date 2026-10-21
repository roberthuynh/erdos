import Erdos1017.ContinuousCertificate
import Erdos1017.RootedTypeLift
import Erdos1017.MultipartiteAccounting

namespace Erdos1017
open scoped BigOperators
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

theorem affine_from_rooted_accounting (C a S q n e : ℝ)
    (hcost : C ≤ a^2*normalizedAffineBudget S q)
    (hn : a*(S+1) = n) (he : 2*e+a^2+a^2*q=n^2) :
    C+(Real.sqrt 7/3)*e ≤ (1+Real.sqrt 7/3)*n^2/4 := by
  have hn2 : a^2*(S+1)^2=n^2 := by nlinarith [congrArg (fun x : ℝ => x^2) hn]
  have hnw := congrArg (fun x : ℝ => (1-Real.sqrt 7/3)*x/4) hn2
  have hew := congrArg (fun x : ℝ => (Real.sqrt 7/3)*x/2) he
  unfold normalizedAffineBudget at hcost
  nlinarith

/-- The full compact residual rectangle now gives an actual original-edge partition. -/
theorem compact_sector_sharp_affine (G : SimpleGraph V) [DecidableRel G.Adj]
    (part : V → Option ι) (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v)
    (hpos : ∀ i, 0 < partSize part i)
    (hSl : (17:ℝ)/8 ≤ ∑ i : ι, (partSize part (some i) : ℝ)/partSize part none)
    (hSh : (∑ i : ι, (partSize part (some i) : ℝ)/partSize part none) ≤ (7:ℝ)/2)
    (hsmallq : (∑ i : ι, ((partSize part (some i) : ℝ)/partSize part none)^2) ≤ (16:ℝ)/25) :
    ∃ P : FractionalPartition G,
      P.cost+(Real.sqrt 7/3)*(G.edgeFinset.card : ℝ) ≤
        (1+Real.sqrt 7/3)*(Fintype.card V : ℝ)^2/4 := by
  let a : ℝ := partSize part none
  let p : ι → ℝ := fun i => (partSize part (some i) : ℝ)/a
  let q := ∑ i, (p i)^2
  let m := Real.sqrt q
  have ha : 0 < a := by dsimp [a]; exact_mod_cast hpos none
  have hp : ∀ i, 0 ≤ p i := fun i => div_nonneg (Nat.cast_nonneg _) ha.le
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hm : 0 ≤ m := Real.sqrt_nonneg _
  have hmsq : m^2=q := Real.sq_sqrt hq
  have hpm (i : ι) : p i ≤ m := by
    have hs : (p i)^2 ≤ q := Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
    nlinarith [hp i]
  have hmcap : m ≤ (4:ℝ)/5 := by
    change q ≤ (16:ℝ)/25 at hsmallq
    nlinarith
  obtain ⟨w,hw,hmom,hcost⟩ := continuous_sharp_selector p m hp hpm hmsq.symm hSl hSh hm hmcap
  obtain ⟨P,hP⟩ := multipartite_partition_of_rooted_law G part hG hpos w hw hmom
  refine ⟨P,?_⟩
  obtain ⟨hn,hqcount,he⟩ := rooted_part_accounting G part hG (hpos none)
  have hc : P.cost ≤ a^2*normalizedAffineBudget (∑ i,p i) q := by
    rw [hmsq] at hcost
    exact hP.trans (mul_le_mul_of_nonneg_left hcost (sq_nonneg a))
  apply affine_from_rooted_accounting P.cost a (∑ i,p i) q
    (Fintype.card V) (G.edgeFinset.card) hc hn
  change 2*(G.edgeFinset.card : ℝ)+a^2+a^2*q=(Fintype.card V : ℝ)^2
  rw [hqcount]
  exact he

theorem large_square_normalized_budget (S q : ℝ) (hS : (17:ℝ)/8 ≤ S) (hq : (16:ℝ)/25 ≤ q) :
    1 ≤ normalizedAffineBudget S q := by
  have hr : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg _
  have hrsq : (Real.sqrt 7)^2=7 := Real.sq_sqrt (by norm_num)
  have hrmax : Real.sqrt 7/3 ≤ (441:ℝ)/500 := by nlinarith
  have hSsq : (25:ℝ)^2/64 ≤ (S+1)^2 := by nlinarith
  have hSw := mul_le_mul_of_nonneg_left hSsq (show 0 ≤ 1-Real.sqrt 7/3 by nlinarith)
  have hqw := mul_le_mul_of_nonneg_left hq (show 0 ≤ Real.sqrt 7/3 by positivity)
  unfold normalizedAffineBudget
  nlinarith

theorem large_square_sharp_affine (G : SimpleGraph V) [DecidableRel G.Adj]
    (part : V → Option ι) (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v)
    (hpos : ∀ i, 0 < partSize part i)
    (hmax : ∀ i, partSize part i ≤ partSize part none)
    (hS : (17:ℝ)/8 ≤ ∑ i : ι, (partSize part (some i) : ℝ)/partSize part none)
    (hq : (16:ℝ)/25 ≤ ∑ i : ι, ((partSize part (some i) : ℝ)/partSize part none)^2) :
    ∃ P : FractionalPartition G,
      P.cost+(Real.sqrt 7/3)*(G.edgeFinset.card : ℝ) ≤
        (1+Real.sqrt 7/3)*(Fintype.card V : ℝ)^2/4 := by
  let a : ℝ := partSize part none
  let p : ι → ℝ := fun i => (partSize part (some i) : ℝ)/a
  have ha : 0 < a := by dsimp [a]; exact_mod_cast hpos none
  obtain ⟨P,hP⟩ := multipartite_partition_le_square ha G part hG (fun i => by dsimp [a]; exact_mod_cast hmax i)
  refine ⟨P,?_⟩
  obtain ⟨hn,hqcount,he⟩ := rooted_part_accounting G part hG (hpos none)
  have hb := large_square_normalized_budget (∑ i,p i) (∑ i,(p i)^2) hS hq
  have hc : P.cost ≤ a^2*normalizedAffineBudget (∑ i,p i) (∑ i,(p i)^2) :=
    hP.trans (by simpa using mul_le_mul_of_nonneg_left hb (sq_nonneg a))
  apply affine_from_rooted_accounting P.cost a (∑ i,p i) (∑ i,(p i)^2)
    (Fintype.card V) (G.edgeFinset.card) hc hn
  change 2*(G.edgeFinset.card : ℝ)+a^2+a^2*(∑ i,(p i)^2)=(Fintype.card V : ℝ)^2
  rw [hqcount]
  exact he

/-- Both square-sum branches cover the entire intermediate-largest-part sector. -/
theorem central_sector_sharp_affine (G : SimpleGraph V) [DecidableRel G.Adj]
    (part : V → Option ι) (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v)
    (hpos : ∀ i, 0 < partSize part i)
    (hmax : ∀ i, partSize part i ≤ partSize part none)
    (hSl : (17:ℝ)/8 ≤ ∑ i : ι, (partSize part (some i) : ℝ)/partSize part none)
    (hSh : (∑ i : ι, (partSize part (some i) : ℝ)/partSize part none) ≤ (7:ℝ)/2) :
    ∃ P : FractionalPartition G,
      P.cost+(Real.sqrt 7/3)*(G.edgeFinset.card : ℝ) ≤
        (1+Real.sqrt 7/3)*(Fintype.card V : ℝ)^2/4 := by
  rcases le_total (∑ i : ι, ((partSize part (some i) : ℝ)/partSize part none)^2) ((16:ℝ)/25) with hq | hq
  · exact compact_sector_sharp_affine G part hG hpos hSl hSh hq
  · exact large_square_sharp_affine G part hG hpos hmax hSl hq

end Erdos1017
