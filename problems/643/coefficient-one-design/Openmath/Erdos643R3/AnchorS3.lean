import Openmath.Erdos643R3.AnchorT1
set_option autoImplicit false
namespace Erdos643R3.AnchorCaps
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound Erdos643R3.SlotModel
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
variable {x y u v w : V}

theorem slotCost_ge_degree_cap {a b c z : V} {n : ℕ}
    (hdeg : (nb H a b c z).card + (nc H a b c z).card ≤ n) :
    1 / (2 * (1 + (n : ℚ))) ≤ slotCost H a b c z := by
  unfold slotCost
  have hnat : ((nb H a b c z).card : ℚ) + ((nc H a b c z).card : ℚ) ≤ n := by
    exact_mod_cast hdeg
  have hb : (0 : ℚ) ≤ ((nb H a b c z).card : ℚ) := Nat.cast_nonneg _
  have hc : (0 : ℚ) ≤ ((nc H a b c z).card : ℚ) := Nat.cast_nonneg _
  apply one_div_le_one_div_of_le (by positivity)
  linarith

/-- The T1 B slots have no x-relation edges, derived from the light group and S1(a). -/
theorem T1_B_no_Rx (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    {s : V} (hs : s ∈ grp H v u x) : nc H v u x s = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hrC := (mem_nc.mp hr).1
  rw [T1_C h] at hrC
  have hrw : r = w := mem_singleton.mp hrC
  subst r
  have hsr := nc_reciprocal hs hr
  rw [T1_w_C_nb h hcard] at hsr
  exact notMem_empty s hsr

/-- Every T1 A slot except y has no v-relation edge. -/
theorem T1_A_no_Rv (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    {z : V} (hz : z ∈ grp H x v u) (hzy : z ≠ y) : nb H x v u z = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hrC := (mem_nb.mp hr).1
  rw [T1_C h] at hrC
  have hrw : r = w := mem_singleton.mp hrC
  subst r
  have hzr := nb_reciprocal hz hr
  rw [T1_w_C_nc h hcard] at hzr
  exact hzy (mem_singleton.mp hzr)

theorem T1_w_B_nb (h : Host H x y u v w) : nb H v u x w = insert y (J H x y u v w) := by
  rw [← v_Ru h,v_Ru_inter h]
  ext z
  constructor
  · intro hz
    obtain ⟨hzA,hzw,huzw⟩ := mem_nb.mp hz
    obtain ⟨hzx,hzv,hzu,hzvu⟩ := mem_grp.mp hzA
    apply mem_erase.mpr
    refine ⟨hzx,mem_inter.mpr ⟨?_,?_⟩⟩
    · apply mem_link.mpr
      refine ⟨by simp [hzu,hzv],?_⟩
      rw [show insert z ({u,v} : Finset V) = {z,v,u} from triple_perm (fun t => by tauto)]
      exact hzvu
    · apply mem_link.mpr
      refine ⟨by simp [hzu,hzw],?_⟩
      rw [show insert z ({u,w} : Finset V) = {u,z,w} from triple_perm (fun t => by tauto)]
      exact huzw
  · intro hz
    obtain ⟨hzx,hz⟩ := mem_erase.mp hz
    obtain ⟨hzP,hzM⟩ := mem_inter.mp hz
    obtain ⟨hznP,hzuv⟩ := mem_link.mp hzP
    obtain ⟨hznM,hzuw⟩ := mem_link.mp hzM
    simp only [mem_insert,mem_singleton,not_or] at hznP hznM
    apply mem_nb.mpr
    refine ⟨mem_grp.mpr ⟨hzx,hznP.2,hznP.1,?_⟩,hznM.2,?_⟩
    · rw [show ({z,v,u} : Finset V) = insert z {u,v} from triple_perm (fun t => by tauto)]
      exact hzuv
    · rw [show ({u,z,w} : Finset V) = insert z {u,w} from triple_perm (fun t => by tauto)]
      exact hzuw

theorem T1_w_B_cost (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    slotCost H v u x w = 1 / (2 * (2 + ((J H x y u v w).card : ℚ))) := by
  have hwB : w ∈ grp H v u x := by
    apply mem_grp.mpr
    refine ⟨h.vw.symm,h.uw.symm,h.xw.symm,?_⟩
    rw [show ({w,u,x} : Finset V) = {x,u,w} from triple_perm (fun t => by tauto)]
    exact h.xuw
  unfold slotCost
  rw [T1_w_B_nb h,T1_B_no_Rx h hcard hwB,card_empty,card_insert_of_notMem]
  · push_cast
    congr 2
    ring
  · simp [J]

def R1 (H : Finset (Finset V)) (x u v w : V) : Finset V := (grp H v u x).erase w
def D1 (H : Finset (Finset V)) (x y u v w : V) : Finset V :=
  ((grp H x v u).erase y) \ J H x y u v w

theorem J_subset_T1_A (h : Host H x y u v w) :
    J H x y u v w ⊆ (grp H x v u).erase y := by
  intro z hz
  obtain ⟨hzPQ,hzn⟩ := mem_sdiff.mp hz
  obtain ⟨hzP,-⟩ := mem_inter.mp hzPQ
  simp only [mem_insert,mem_singleton,not_or] at hzn
  apply mem_erase.mpr
  refine ⟨hzn.2,?_⟩
  unfold grp
  rw [pair_comm v u]
  exact mem_erase.mpr ⟨hzn.1,hzP⟩

/-- S3's D1 degree cap, obtained by excluding w from the actual neighbours. -/
theorem T1_D1_cap (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    {z : V} (hz : z ∈ D1 H x y u v w) :
    (nb H x v u z).card + (nc H x v u z).card ≤ (R1 H x u v w).card := by
  obtain ⟨hzAy,hzJ⟩ := mem_sdiff.mp hz
  obtain ⟨hzy,hzA⟩ := mem_erase.mp hzAy
  have hsub : nc H x v u z ⊆ R1 H x u v w := by
    intro s hs
    have hsB := (mem_nc.mp hs).1
    apply mem_erase.mpr
    refine ⟨?_,hsB⟩
    intro he
    subst s
    have hzw := nc_reciprocal hzA hs
    rw [T1_w_B_nb h] at hzw
    simp only [mem_insert] at hzw
    exact hzw.elim hzy hzJ
  rw [T1_A_no_Rv h hcard hzA hzy,card_empty,zero_add]
  exact card_le_card hsub

/-- S3's R1 degree cap, obtained by excluding y from the actual neighbours. -/
theorem T1_R1_cap (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    {s : V} (hs : s ∈ R1 H x u v w) :
    (nb H v u x s).card + (nc H v u x s).card ≤
      ((grp H x v u).erase y).card := by
  obtain ⟨hsw,hsB⟩ := mem_erase.mp hs
  have hsub : nb H v u x s ⊆ (grp H x v u).erase y := by
    intro z hz
    have hzA := (mem_nb.mp hz).1
    apply mem_erase.mpr
    refine ⟨?_,hzA⟩
    intro he
    subst z
    have hsy := nb_reciprocal hsB hz
    rw [(T1_y_neighbours h).2] at hsy
    exact hsw (mem_singleton.mp hsy)
  rw [T1_B_no_Rx h hcard hsB,card_empty,add_zero]
  exact card_le_card hsub

theorem nc_as_erase (a b c z : V) : nc H a b c z =
    ((link H {c,a}).filter (fun s => rel H c z s)).erase b := by
  simp only [nc,grp,filter_erase]

/-- The J1 slots have exactly the same cost in T1 and in the anchor. -/
theorem T1_J_cost (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    {z : V} (hz : z ∈ J H x y u v w) : slotCost H x v u z = slotCost H x u w z := by
  have hzAy := J_subset_T1_A h hz
  obtain ⟨hzy,hzA⟩ := mem_erase.mp hzAy
  have hzAu := J_subset_Au h hcard hz
  have hAzero := (mem_filter.mp hzAu).2.2
  have hTzero : (nb H x v u z).card = 0 := by rw [T1_A_no_Rv h hcard hzA hzy,card_empty]
  let N := (link H {u,x}).filter (fun s => rel H u z s)
  have hvN : v ∈ N := by
    apply mem_filter.mpr
    refine ⟨?_,?_⟩
    · have hvXu := mem_of_mem_erase (v_group_C h)
      simpa [pair_comm x u] using hvXu
    · obtain ⟨hzPQ,-⟩ := mem_sdiff.mp hz
      have hzP := (mem_inter.mp hzPQ).1
      obtain ⟨hzn,hzuv⟩ := mem_link.mp hzP
      simp only [mem_insert,mem_singleton,not_or] at hzn
      refine ⟨hzn.2,?_⟩
      rw [show ({u,z,v} : Finset V) = insert z {u,v} from triple_perm (fun t => by tauto)]
      exact hzuv
  have hwN : w ∈ N := by
    apply mem_filter.mpr
    refine ⟨?_,?_⟩
    · apply mem_link.mpr
      refine ⟨by simp [h.uw.symm,h.xw.symm],?_⟩
      rw [show insert w ({u,x} : Finset V) = {x,u,w} from triple_perm (fun t => by tauto)]
      exact h.xuw
    · obtain ⟨hzPQ,-⟩ := mem_sdiff.mp hz
      have hzM := (mem_inter.mp hzPQ).2
      obtain ⟨hzn,hzuw⟩ := mem_link.mp hzM
      simp only [mem_insert,mem_singleton,not_or] at hzn
      refine ⟨hzn.2,?_⟩
      rw [show ({u,z,w} : Finset V) = insert z {u,w} from triple_perm (fun t => by tauto)]
      exact hzuw
  have hdeg : (nc H x v u z).card = (nb H x u w z).card := by
    rw [nb_swap_nc x w u z,nc_as_erase,nc_as_erase]
    change (N.erase v).card = (N.erase w).card
    rw [card_erase_of_mem hvN,card_erase_of_mem hwN]
  unfold slotCost
  rw [hTzero,hAzero]
  simp only [Nat.cast_zero,add_zero,zero_add]
  rw [hdeg]

/-- S3, with the group terms retained in the existing exact slot notation. -/
theorem S3_slot_bound (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    groupSigma H x v u + groupSigma H v u x +
      1 / (2 * (2 + ((J H x y u v w).card : ℚ))) +
      (∑ z ∈ J H x y u v w, slotCost H x u w z) +
      ((D1 H x y u v w).card : ℚ) / (2 * (1 + ((R1 H x u v w).card : ℚ))) +
      ((R1 H x u v w).card : ℚ) / (2 * (1 + (((grp H x v u).erase y).card : ℚ))) ≤
    L1Top.charge H {x,u,v} + 13/12 := by
  have hA := J_subset_T1_A h
  have hsumA : (∑ z ∈ D1 H x y u v w, slotCost H x v u z) +
      (∑ z ∈ J H x y u v w, slotCost H x v u z) =
      ∑ z ∈ (grp H x v u).erase y, slotCost H x v u z := by
    exact sum_sdiff hA
  have hcostJ : (∑ z ∈ J H x y u v w, slotCost H x v u z) =
      ∑ z ∈ J H x y u v w, slotCost H x u w z :=
    sum_congr rfl (fun z hz => T1_J_cost h hcard hz)
  have hD : ((D1 H x y u v w).card : ℚ) / (2 * (1 + ((R1 H x u v w).card : ℚ))) ≤
      ∑ z ∈ D1 H x y u v w, slotCost H x v u z := by
    have hs := sum_le_sum (s := D1 H x y u v w)
      (fun z hz => slotCost_ge_degree_cap (T1_D1_cap h hcard hz))
    simpa only [sum_const,nsmul_eq_mul,mul_one_div] using hs
  have hR : ((R1 H x u v w).card : ℚ) / (2 * (1 + (((grp H x v u).erase y).card : ℚ))) ≤
      ∑ s ∈ R1 H x u v w, slotCost H v u x s := by
    have hs := sum_le_sum (s := R1 H x u v w)
      (fun s hs => slotCost_ge_degree_cap (T1_R1_cap h hcard hs))
    simpa only [sum_const,nsmul_eq_mul,mul_one_div] using hs
  have hwB : w ∈ grp H v u x := by
    apply mem_grp.mpr
    refine ⟨h.vw.symm,h.uw.symm,h.xw.symm,?_⟩
    rw [show ({w,u,x} : Finset V) = {x,u,w} from triple_perm (fun t => by tauto)]
    exact h.xuw
  have hsumB : (∑ s ∈ R1 H x u v w, slotCost H v u x s) +
      slotCost H v u x w = ∑ s ∈ grp H v u x, slotCost H v u x s :=
    sum_erase_add _ _ hwB
  rw [T1_w_B_cost h hcard] at hsumB
  rw [T1_charge_decomposition h hcard]
  linarith

theorem T1_A_card (h : Host H x y u v w) :
    (grp H x v u).card = 1 + (J H x y u v w).card + (D1 H x y u v w).card := by
  have hcard := card_sdiff_add_card_eq_card (J_subset_T1_A h)
  have hyA : y ∈ grp H x v u := by
    apply mem_grp.mpr
    refine ⟨h.xy.symm,h.yv,h.yu,?_⟩
    rw [show ({y,v,u} : Finset V) = {y,u,v} from triple_perm (fun t => by tauto)]
    exact h.yuv
  have he := card_erase_add_one hyA
  change (D1 H x y u v w).card + (J H x y u v w).card = _ at hcard
  omega

theorem T1_B_card (h : Host H x y u v w) :
    (grp H v u x).card = 1 + (R1 H x u v w).card := by
  have hwB : w ∈ grp H v u x := by
    apply mem_grp.mpr
    refine ⟨h.vw.symm,h.uw.symm,h.xw.symm,?_⟩
    rw [show ({w,u,x} : Finset V) = {x,u,w} from triple_perm (fun t => by tauto)]
    exact h.xuw
  have he := card_erase_add_one hwB
  change (R1 H x u v w).card + 1 = _ at he
  omega

theorem T1_Ay_card (h : Host H x y u v w) :
    ((grp H x v u).erase y).card = (J H x y u v w).card + (D1 H x y u v w).card := by
  have hc := card_sdiff_add_card_eq_card (J_subset_T1_A h)
  change (D1 H x y u v w).card + (J H x y u v w).card = _ at hc
  omega

/-- Lemma S3 with all variables defined from the actual host finsets. -/
theorem S3 (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    1 / (2 + ((J H x y u v w).card : ℚ) + ((D1 H x y u v w).card : ℚ)) +
      1 / (2 + ((R1 H x u v w).card : ℚ)) +
      1 / (2 * (2 + ((J H x y u v w).card : ℚ))) +
      (∑ z ∈ J H x y u v w, slotCost H x u w z) +
      ((D1 H x y u v w).card : ℚ) / (2 * (1 + ((R1 H x u v w).card : ℚ))) +
      ((R1 H x u v w).card : ℚ) /
        (2 * (1 + ((J H x y u v w).card : ℚ) + ((D1 H x y u v w).card : ℚ))) ≤
    L1Top.charge H {x,u,v} + 13/12 := by
  have hs := S3_slot_bound h hcard
  unfold groupSigma at hs
  rw [T1_A_card h,T1_B_card h,T1_Ay_card h] at hs
  push_cast at hs
  convert hs using 1 <;> congr 2 <;> ring

theorem R1_eq (x u v w : V) :
    R1 H x u v w = (link H {x,u}) \ {v,w} := by
  ext s
  simp only [R1,grp,mem_erase,mem_sdiff,mem_insert,mem_singleton,not_or]
  rw [pair_comm u x]
  tauto

theorem D1_eq (x y u v w : V) : D1 H x y u v w =
    (link H {u,v}) \ ({x,y} ∪ J H x y u v w) := by
  ext s
  simp only [D1,grp,mem_erase,mem_sdiff,mem_union,mem_insert,mem_singleton,not_or]
  rw [pair_comm v u]
  tauto

end Erdos643R3.AnchorCaps
