import Openmath.Erdos643R3.AnchorCaps
set_option autoImplicit false
namespace Erdos643R3.AnchorCaps
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound Erdos643R3.SlotModel
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

theorem grp_swap (a b c : V) : grp H a c b = grp H a b c := by
  unfold grp; rw [pair_comm c b]

theorem nb_swap_nc (a b c z : V) : nb H a c b z = nc H a b c z := by
  ext s
  simp only [mem_nb,mem_nc]
  rw [grp_swap b c a]
  constructor
  · rintro ⟨hs,hzs,hcsz⟩
    refine ⟨hs,hzs.symm,?_⟩
    rw [show ({c,z,s} : Finset V) = {c,s,z} from triple_perm (fun t => by tauto)]
    exact hcsz
  · rintro ⟨hs,hzs,hczs⟩
    refine ⟨hs,hzs.symm,?_⟩
    rw [show ({c,s,z} : Finset V) = {c,z,s} from triple_perm (fun t => by tauto)]
    exact hczs

theorem nc_swap_nb (a b c z : V) : nc H a c b z = nb H a b c z := by
  exact (nb_swap_nc a c b z).symm

theorem fset_swap_gset (a b c : V) : fset H a c b = gset H a b c := by
  unfold fset gset
  rw [grp_swap a b c]
  apply filter_congr
  intro z hz
  rw [nb_swap_nc a b c z,nc_swap_nb a b c z]

theorem gset_swap_fset (a b c : V) : gset H a c b = fset H a b c :=
  (fset_swap_gset a c b).symm

theorem tset_swap (a b c : V) : tset H a c b = tset H a b c := by
  unfold tset
  rw [grp_swap a b c]
  apply filter_congr
  intro z hz
  rw [nb_swap_nc a b c z,nc_swap_nb a b c z]
  exact and_comm

theorem iset_swap (a b c : V) : iset H a c b = iset H a b c := by
  unfold iset
  rw [grp_swap a b c]
  apply filter_congr
  intro z hz
  rw [nb_swap_nc a b c z,nc_swap_nb a b c z]
  exact and_comm

theorem slotCost_swap (a b c z : V) : slotCost H a c b z = slotCost H a b c z := by
  unfold slotCost
  rw [nb_swap_nc a b c z,nc_swap_nb a b c z]
  congr 2
  ring

variable {x y u v w : V}

theorem J_subset_Au (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    J H x y u v w ⊆ gset H x u w := by
  intro z hz
  have hzv : z ∈ nc H w x u v := by rw [v_Ru h]; exact mem_insert_of_mem hz
  have hzy : z ≠ y := by
    have ht := (mem_sdiff.mp hz).2
    simp only [mem_insert,mem_singleton,not_or] at ht
    exact ht.2
  have hzA := (mem_nc.mp hzv).1
  have hvz := nc_reciprocal (v_group_C h) hzv
  have hb : 0 < (nb H x u w z).card := card_pos.mpr ⟨v,hvz⟩
  have hc : (nc H x u w z).card = 0 := by
    by_contra hn
    have hz2 : z ∈ tset H x u w := mem_filter.mpr ⟨hzA,hb,Nat.pos_of_ne_zero hn⟩
    rw [only_type2_A h hcard] at hz2
    exact hzy (mem_singleton.mp hz2)
  exact mem_filter.mpr ⟨hzA,hb,hc⟩

theorem v_type1_C (h : Host H x y u v w) : v ∈ fset H w x u := by
  apply mem_filter.mpr
  refine ⟨v_group_C h,?_,?_⟩
  · apply card_pos.mpr
    refine ⟨y,?_⟩
    rw [v_Ru h]
    exact mem_insert_self y _
  · rw [v_no_Rx_C h,card_empty]

theorem v_degree_C_le_Au (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    (nb H w x u v).card + (nc H w x u v).card ≤ 1 + (gset H x u w).card := by
  rw [v_degree_C h]
  have := card_le_card (J_subset_Au h hcard)
  omega

end Erdos643R3.AnchorCaps
