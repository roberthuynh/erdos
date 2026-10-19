import Openmath.Erdos643R3.AnchorS3
import Openmath.Erdos643R3.AnchorDecomposition
import Openmath.Erdos643R3.PsiLoss

set_option autoImplicit false
open scoped BigOperators
namespace Erdos643R3.HostPsi
open Finset
open Erdos643R3.Identity Erdos643R3.SlotModel Erdos643R3.AnchorCaps
open Erdos643R3.AnchorW Erdos643R3.AnchorDecomposition Erdos643R3.GeneralizedPsi
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
variable {x y u v w : V}

def EU (H : Finset (Finset V)) (x y u v w : V) : Finset V :=
  gset H x u w \ J H x y u v w

theorem Au_card (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    (gset H x u w).card = (J H x y u v w).card + (EU H x y u v w).card := by
  have hc := card_sdiff_add_card_eq_card (J_subset_Au h hcard)
  change (EU H x y u v w).card + (J H x y u v w).card = _ at hc
  omega

theorem C_card (h : Host H x y u v w) :
    (grp H w x u).card = 1 + (R1 H x u v w).card := by
  have he := card_erase_add_one (v_group_C h)
  have hid : (grp H w x u).erase v = R1 H x u v w := by
    ext s
    simp only [R1,grp,mem_erase]
    rw [pair_comm u x]
    tauto
  rw [hid] at he
  omega

theorem EU_not_v_adj (h : Host H x y u v w) {z : V} (hz : z ∈ EU H x y u v w) :
    v ∉ nb H x u w z := by
  obtain ⟨hzAu,hzJ⟩ := mem_sdiff.mp hz
  obtain ⟨hzA,-,hzero⟩ := mem_filter.mp hzAu
  intro hv
  have hzv := nb_reciprocal hzA hv
  rw [v_Ru h] at hzv
  rcases mem_insert.mp hzv with hzy | hzJ'
  · subst z
    rw [(y_neighbours h).2,card_singleton] at hzero
    omega
  · exact hzJ hzJ'

theorem EU_degree_cap (h : Host H x y u v w) {z : V} (hz : z ∈ EU H x y u v w) :
    degree H x u w z ≤ (RU H x u v w).card + (tset H w x u).card := by
  have hzAu := (mem_sdiff.mp hz).1
  obtain ⟨hzA,-,hzero⟩ := mem_filter.mp hzAu
  have hsub : nb H x u w z ⊆ RU H x u v w ∪ tset H w x u := by
    intro s hs
    have hc := Au_neighbours_classes (v := v) hzA hs
    rcases mem_insert.mp hc with hsv | hs'
    · exact False.elim (EU_not_v_adj h hz (hsv ▸ hs))
    · exact hs'
  have hc := card_le_card hsub
  have hu := card_union_le (RU H x u v w) (tset H w x u)
  unfold degree
  omega

theorem EU_ordinary_cap (h : Host H x y u v w) {p z : V}
    (hz : z ∈ EU H x y u v w) (hzp : z ≠ p)
    (hp : ∀ r ∈ tset H w x u, nc H w x u r = {p}) :
    degree H x u w z ≤ (RU H x u v w).card := by
  have hzAu := (mem_sdiff.mp hz).1
  obtain ⟨hzA,-,hzero⟩ := mem_filter.mp hzAu
  have hsub : nb H x u w z ⊆ RU H x u v w := by
    intro s hs
    have hc := Au_neighbours_classes (v := v) hzA hs
    rcases mem_insert.mp hc with hsv | hs'
    · exact False.elim (EU_not_v_adj h hz (hsv ▸ hs))
    · rcases mem_union.mp hs' with hsRU | hs2
      · exact hsRU
      · have hzs := nb_reciprocal hzA hs
        rw [hp s hs2] at hzs
        exact False.elim (hzp (mem_singleton.mp hzs))
  have hc := card_le_card hsub
  unfold degree
  omega

theorem RU_degree_cap (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    {s : V} (hs : s ∈ RU H x u v w) :
    degree H w x u s ≤ (J H x y u v w).card + (EU H x y u v w).card := by
  obtain ⟨hsv,hsf⟩ := mem_erase.mp hs
  obtain ⟨hsC,-,hzero⟩ := mem_filter.mp hsf
  have hc := Ru_degree_cap h hcard hsC hsv
  rw [Au_card h hcard] at hc
  unfold degree
  omega

theorem v_cost (h : Host H x y u v w) :
    slotCost H w x u v = 1 / (2 * (2 + ((J H x y u v w).card : ℚ))) := by
  rw [← cost_degree]
  unfold WBox.slotCost degree
  rw [v_degree_C h]
  push_cast
  congr 2
  ring

/-- A single actual exceptional vertex pays exactly one reciprocal loss. -/
theorem sum_cost_one_exception (s : Finset V) (a b c p : V) (n m : ℕ)
    (hcap : ∀ z ∈ s, degree H a b c z ≤ n + m)
    (hothers : ∀ z ∈ s, z ≠ p → degree H a b c z ≤ n) :
    (s.card : ℚ) / (2 * (1 + (n : ℚ))) -
      (if p ∈ s then lossE n m else 0) ≤ ∑ z ∈ s, slotCost H a b c z := by
  by_cases hp : p ∈ s
  · have hc := WBox.sum_cost_cap (s.erase p) (degree H a b c) n (by
      intro z hz
      exact hothers z (mem_erase.mp hz).2 (mem_erase.mp hz).1)
    have hp' := WBox.slotCost_antitone (hcap p hp)
    have he := sum_erase_add s (fun z => slotCost H a b c z) hp
    have hn := card_erase_add_one hp
    have hn' : ((s.erase p).card : ℚ) + 1 = s.card := by exact_mod_cast hn
    simp only [cost_degree] at hc hp'
    rw [if_pos hp]
    unfold lossE
    change 1 / (2 * (1 + ((n + m : ℕ) : ℚ))) ≤ slotCost H a b c p at hp'
    push_cast at hp'
    rw [← add_assoc] at hp'
    rw [show (s.card : ℚ) = (s.erase p).card + 1 by linarith]
    rw [add_div]
    linarith
  · rw [if_neg hp,sub_zero]
    have hc := WBox.sum_cost_cap s (degree H a b c) n (by
      intro z hz
      exact hothers z hz (fun hzp => hp (hzp ▸ hz)))
    simpa only [cost_degree] using hc

/-- The actual ordinary plus exceptional C slots fit inside R. -/
theorem RU_type2_card_le (h : Host H x y u v w) :
    (RU H x u v w).card + (tset H w x u).card ≤ (R1 H x u v w).card := by
  have hd : Disjoint (RU H x u v w) (tset H w x u) := by
    apply disjoint_left.mpr
    intro z hz hz2
    have hzero := (mem_filter.mp (mem_erase.mp hz).2).2.2
    have hpos := (mem_filter.mp hz2).2.1
    omega
  have hsub : RU H x u v w ∪ tset H w x u ⊆ (grp H w x u).erase v := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · exact mem_erase.mpr ⟨(mem_erase.mp hz).1,(mem_filter.mp (mem_erase.mp hz).2).1⟩
    · apply mem_erase.mpr
      refine ⟨?_,(mem_filter.mp hz).1⟩
      intro hzv
      have hp := (mem_filter.mp hz).2.1
      rw [hzv,v_no_Rx_C h,card_empty] at hp
      omega
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hd,card_erase_of_mem (v_group_C h),C_card h] at hc
  omega

theorem uMinus_split (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    uMinus H x u w =
      1 / (2 + ((R1 H x u v w).card : ℚ)) +
      1 / (2 * (2 + ((J H x y u v w).card : ℚ))) +
      (∑ s ∈ RU H x u v w, slotCost H w x u s) +
      (∑ z ∈ J H x y u v w, slotCost H x u w z) +
      (∑ z ∈ EU H x y u v w, slotCost H x u w z) := by
  have hC := sum_erase_add (fset H w x u) (fun z => slotCost H w x u z) (v_type1_C h)
  change (∑ z ∈ RU H x u v w, slotCost H w x u z) + _ = _ at hC
  rw [v_cost h] at hC
  have hA := sum_sdiff (f := fun z => slotCost H x u w z) (J_subset_Au h hcard)
  change (∑ z ∈ EU H x y u v w, slotCost H x u w z) + _ = _ at hA
  have hG : groupSigma H w x u = 1 / (2 + ((R1 H x u v w).card : ℚ)) := by
    unfold groupSigma
    rw [C_card h]
    push_cast
    congr 1
    ring
  unfold uMinus
  rw [hG]
  linarith

theorem uMinus_S1_raw (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    2 / (2 + ((R1 H x u v w).card : ℚ)) +
      1 / (2 + ((J H x y u v w).card : ℚ) + (D1 H x y u v w).card) +
      1 / (2 + ((J H x y u v w).card : ℚ)) +
      2 * (∑ z ∈ J H x y u v w, slotCost H x u w z) +
      ((D1 H x y u v w).card : ℚ) / (2 * (1 + ((R1 H x u v w).card : ℚ))) +
      ((R1 H x u v w).card : ℚ) /
        (2 * (1 + ((J H x y u v w).card : ℚ) + (D1 H x y u v w).card)) +
      (∑ z ∈ EU H x y u v w, slotCost H x u w z) +
      ((RU H x u v w).card : ℚ) /
        (2 * (1 + ((J H x y u v w).card : ℚ) + (EU H x y u v w).card)) ≤
    uMinus H x u w + (L1Top.charge H {x,u,v} + 13/12) := by
  have hs := S3 h hcard
  have hu := uMinus_split h hcard
  have hr := WBox.sum_cost_cap (RU H x u v w) (degree H w x u)
    ((J H x y u v w).card + (EU H x y u v w).card)
    (fun s hs => RU_degree_cap h hcard hs)
  simp only [cost_degree] at hr
  push_cast at hr
  rw [← add_assoc] at hr
  have hid (j : ℚ) : 1 / (2 + j) = 2 * (1 / (2 * (2 + j))) := by
    rw [div_mul_eq_div_div]
    ring
  rw [hid]
  have hid2 (r : ℚ) : 2 / (2 + r) = 2 * (1 / (2 + r)) := by ring
  rw [hid2]
  linarith

theorem lossE_nonneg (k m : ℕ) : 0 ≤ lossE k m := by
  unfold lossE
  have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hb : 1 / (2 * (1 + (k : ℚ) + m)) ≤ 1 / (2 * (1 + (k : ℚ))) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- The §7.7 inequality at a common partner, obtained from the actual host sums. -/
theorem host_bound_at_partner (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (p : V) (hp : ∀ r ∈ tset H w x u, nc H w x u r = {p}) :
    PsiR (J H x y u v w).card (D1 H x y u v w).card (EU H x y u v w).card
      (R1 H x u v w).card (RU H x u v w).card -
      exceptionalLoss (decide (p ∈ J H x y u v w)) (RU H x u v w).card (tset H w x u).card ≤
    uMinus H x u w + (L1Top.charge H {x,u,v} + 13/12) := by
  have hJ := sum_cost_one_exception (J H x y u v w) x u w p
    (1 + (RU H x u v w).card) (tset H w x u).card
    (fun z hz => Au_degree_cap (J_subset_Au h hcard hz))
    (fun z hz hzp => Au_ordinary_cap (J_subset_Au h hcard hz) hzp hp)
  have hE := sum_cost_one_exception (EU H x y u v w) x u w p
    (RU H x u v w).card (tset H w x u).card
    (fun z hz => EU_degree_cap h hz)
    (fun z hz hzp => EU_ordinary_cap h hz hzp hp)
  have hraw := uMinus_S1_raw h hcard
  have hdouble (k m : ℕ) : 2 * lossE (1+k) m = lossJ k m := by
    unfold lossE lossJ
    push_cast
    field_simp
    ring
  have hnorm (j k : ℕ) :
      2 * ((j : ℚ) / (2 * (1 + ((1 + k : ℕ) : ℚ)))) = (j : ℚ) / (2 + (k : ℚ)) := by
    push_cast
    field_simp
    ring
  have hJ2 := mul_le_mul_of_nonneg_left hJ (show (0 : ℚ) ≤ 2 by norm_num)
  rw [mul_sub,hnorm] at hJ2
  by_cases hpJ : p ∈ J H x y u v w
  · have hpE : p ∉ EU H x y u v w := fun hpE => (mem_sdiff.mp hpE).2 hpJ
    rw [if_pos hpJ,hdouble] at hJ2
    rw [if_neg hpE,sub_zero] at hE
    simp only [exceptionalLoss,decide_eq_true hpJ, ↓reduceIte]
    unfold PsiR
    linarith
  · rw [if_neg hpJ,mul_zero,sub_zero] at hJ2
    have he' : ((EU H x y u v w).card : ℚ) / (2 * (1 + ((RU H x u v w).card : ℚ))) -
        lossE (RU H x u v w).card (tset H w x u).card ≤
        ∑ z ∈ EU H x y u v w, slotCost H x u w z := by
      split_ifs at hE with hpE
      · exact hE
      · have hn := lossE_nonneg (RU H x u v w).card (tset H w x u).card
        linarith
    simp only [exceptionalLoss,decide_eq_false hpJ, Bool.false_eq_true, ↓reduceIte]
    unfold PsiR
    linarith

/-- The host supplies both the actual loss form and its required location. -/
theorem host_psi_bridge (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    ∃ inJ : Bool,
      (inJ = false → 0 < (tset H w x u).card → 1 ≤ (EU H x y u v w).card) ∧
      PsiR (J H x y u v w).card (D1 H x y u v w).card (EU H x y u v w).card
        (R1 H x u v w).card (RU H x u v w).card -
        exceptionalLoss inJ (RU H x u v w).card (tset H w x u).card ≤
      uMinus H x u w + (L1Top.charge H {x,u,v} + 13/12) := by
  by_cases hn : (tset H w x u).Nonempty
  · obtain ⟨p,hpAu,-,-,hp⟩ := shared_partner_C h hcard hn
    refine ⟨decide (p ∈ J H x y u v w),?_,host_bound_at_partner h hcard p (fun r hr => (hp r hr).2)⟩
    intro hpJ hm
    have hpJ' : p ∉ J H x y u v w := of_decide_eq_false hpJ
    exact one_le_card.mpr ⟨p,mem_sdiff.mpr ⟨hpAu,hpJ'⟩⟩
  · have hempty := not_nonempty_iff_eq_empty.mp hn
    refine ⟨decide (x ∈ J H x y u v w),?_,host_bound_at_partner h hcard x ?_⟩
    · intro hx hm
      rw [hempty,card_empty] at hm
      omega
    · intro r hr
      rw [hempty] at hr
      exact False.elim (notMem_empty r hr)

theorem host_L9 (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    G3hpArith.L9 (J H x y u v w).card (D1 H x y u v w).card (R1 H x u v w).card ≤
      L1Top.charge H {x,u,v} + 13/12 := by
  have hs := S3 h hcard
  have hkm := RU_type2_card_le h
  have hjcap : ∀ z ∈ J H x y u v w, degree H x u w z ≤ 1 + (R1 H x u v w).card := by
    intro z hz
    have hc := Au_degree_cap (v := v) (J_subset_Au h hcard hz)
    change degree H x u w z ≤ _ at hc
    omega
  have hj := WBox.sum_cost_cap (J H x y u v w) (degree H x u w)
    (1 + (R1 H x u v w).card) hjcap
  simp only [cost_degree] at hj
  push_cast at hj
  rw [show (1 : ℚ) + (1 + ((R1 H x u v w).card : ℚ)) = 2 + (R1 H x u v w).card by ring] at hj
  unfold G3hpArith.L9
  linarith

theorem R1_pos_of_heavy (h : Host H x y u v w)
    (hheavy : 3 ≤ codeg H {x,u}) : 1 ≤ (R1 H x u v w).card := by
  have hT : ({w,x,u} : Finset V) ∈ H := by
    rw [show ({w,x,u} : Finset V) = {x,u,w} from triple_perm (fun t => by tauto)]
    exact h.xuw
  have hc := codeg_eq_one_add_card_grp hT h.uniform
  rw [C_card h] at hc
  have hh : (3 : ℚ) ≤ codeg H {x,u} := by exact_mod_cast hheavy
  have hr : (1 : ℚ) ≤ (R1 H x u v w).card := by
    push_cast at hc
    linarith
  exact_mod_cast hr

end Erdos643R3.HostPsi
